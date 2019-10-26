// Copyright 2017 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package prog

import (
	"fmt"
	"strings"
)

const (
	// Special reference to the outer struct used in len targets.
	ParentRef = "parent"
	// Special reference directly to syscall arguments used in len targets.
	SyscallRef = "syscall"
	// Special reference to arbitrary element of array.
	ElemRef = "elem"
)

func (r *randGen) assignSizes(args []Arg, parentsMap map[Arg]Arg, syscallArgs []Arg, autos map[Arg]bool) {
	for _, arg := range args {
		if arg = InnerArg(arg); arg == nil {
			continue // Pointer to optional len field, no need to fill in value.
		}
		typ, ok := arg.Type().(*LenType)
		if !ok {
			continue
		}
		if autos != nil {
			if !autos[arg] {
				continue
			}
			delete(autos, arg)
		}
		a := arg.(*ConstArg)
		if typ.Path[0] == SyscallRef {
			r.assignSize(a, nil, typ.Path[1:], syscallArgs, parentsMap)
		} else {
			r.assignSize(a, a, typ.Path, args, parentsMap)
		}
	}
}

func (r *randGen) assignSize(dst *ConstArg, pos Arg, path []string, args []Arg, parentsMap map[Arg]Arg) {
	elem := path[0]
	path = path[1:]
	var offset uint64
	for _, buf := range args {
		if elem != buf.Type().FieldName() {
			if !buf.Type().BitfieldMiddle() {
				offset += buf.Size()
			}
			continue
		}
		buf = InnerArg(buf)
		if buf == nil {
			dst.Val = 0 // target is an optional pointer
			return
		}
		if len(path) == 0 {
			dst.Val = r.target.computeSize(buf, offset, dst.Type().(*LenType))
		} else if _, ok := buf.(*DataArg); ok && path[0] == ElemRef && len(path) == 1 {
			if r.Rand != nil {
				bitSize := dst.Type().(*LenType).BitSize
				dst.Val = offset*8/bitSize + r.rand(int(buf.Size()*8/bitSize))
			}
		} else {
			r.assignSize(dst, buf, path, buf.(*GroupArg).Inner, parentsMap)
		}
		return
	}
	if elem == ParentRef {
		buf := parentsMap[pos]
		if len(path) == 0 {
			dst.Val = r.target.computeSize(buf, noOffset, dst.Type().(*LenType))
		} else {
			r.assignSize(dst, buf, path, buf.(*GroupArg).Inner, parentsMap)
		}
		return
	}
	if elem == ElemRef {
		if r.Rand != nil {
			if len(args) == 0 {
				// If target array is empty, we default to 0.
				dst.Val = 0
				return
			}
			buf := args[r.rand(len(args))]
			if len(path) == 0 {
				dst.Val = r.target.computeSize(buf, offset, dst.Type().(*LenType))
			} else {
				r.assignSize(dst, buf, path, buf.(*GroupArg).Inner, parentsMap)
			}
		}
		return
	}
	for buf := parentsMap[pos]; buf != nil; buf = parentsMap[buf] {
		parentName := buf.Type().Name()
		if pos := strings.IndexByte(parentName, '['); pos != -1 {
			// For template parents, strip arguments.
			parentName = parentName[:pos]
		}
		if elem != parentName {
			continue
		}
		if len(path) == 0 {
			dst.Val = r.target.computeSize(buf, noOffset, dst.Type().(*LenType))
		} else {
			r.assignSize(dst, buf, path, buf.(*GroupArg).Inner, parentsMap)
		}
		return
	}
	var argNames []string
	for _, arg := range args {
		argNames = append(argNames, arg.Type().FieldName())
	}
	panic(fmt.Sprintf("len field %q references non existent field %q, pos=%q/%q, argsMap: %+v",
		dst.Type().FieldName(), elem, pos.Type().Name(), pos.Type().FieldName(), argNames))
}

const noOffset = ^uint64(0)

func (target *Target) computeSize(arg Arg, offset uint64, lenType *LenType) uint64 {
	if lenType.Offset {
		if offset == noOffset {
			panic("offset of a non-field")
		}
		return offset * 8 / lenType.BitSize
	}
	bitSize := lenType.BitSize
	if bitSize == 0 {
		bitSize = 8
	}
	switch arg.Type().(type) {
	case *VmaType:
		a := arg.(*PointerArg)
		return a.VmaSize * 8 / bitSize
	case *ArrayType:
		a := arg.(*GroupArg)
		if lenType.BitSize != 0 {
			return a.Size() * 8 / bitSize
		}
		return uint64(len(a.Inner))
	default:
		return arg.Size() * 8 / bitSize
	}
}

func (r *randGen) assignSizesArray(args []Arg, autos map[Arg]bool) {
	parentsMap := make(map[Arg]Arg)
	for _, arg := range args {
		ForeachSubArg(arg, func(arg Arg, _ *ArgCtx) {
			switch arg.Type().(type) {
			case *StructType, *ArrayType:
				for _, field := range arg.(*GroupArg).Inner {
					parentsMap[InnerArg(field)] = arg
				}
			case *UnionType:
				parentsMap[InnerArg(arg.(*UnionArg).Option)] = arg
			}
		})
	}
	r.assignSizes(args, parentsMap, args, autos)
	for _, arg := range args {
		ForeachSubArg(arg, func(arg Arg, _ *ArgCtx) {
			switch arg.Type().(type) {
			case *StructType, *ArrayType:
				r.assignSizes(arg.(*GroupArg).Inner, parentsMap, args, autos)
			case *UnionType:
				r.assignSizes([]Arg{arg.(*UnionArg).Option}, parentsMap, args, autos)
			}
		})
	}
}

func (r *randGen) assignSizesCall(c *Call) {
	r.assignSizesArray(c.Args, nil)
}

func (r *randGen) mutateSize(arg *ConstArg, parent []Arg) bool {
	typ := arg.Type().(*LenType)
	elemSize := typ.BitSize / 8
	if elemSize == 0 {
		elemSize = 1
		// TODO(dvyukov): implement path support for size mutation.
		if len(typ.Path) == 1 {
			for _, field := range parent {
				if typ.Path[0] != field.Type().FieldName() {
					continue
				}
				if inner := InnerArg(field); inner != nil {
					switch targetType := inner.Type().(type) {
					case *VmaType:
						return false
					case *ArrayType:
						if targetType.Type.Varlen() {
							return false
						}
						elemSize = targetType.Type.Size()
					}
				}
				break
			}
		}
	}
	if r.oneOf(100) {
		arg.Val = r.rand64()
		return true
	}
	if r.bin() {
		// Small adjustment to trigger missed size checks.
		if arg.Val != 0 && r.bin() {
			arg.Val = r.randRangeInt(0, arg.Val-1, arg.Type().TypeBitSize(), 0)
		} else {
			arg.Val = r.randRangeInt(arg.Val+1, arg.Val+1000, arg.Type().TypeBitSize(), 0)
		}
		return true
	}
	// Try to provoke int overflows.
	max := ^uint64(0)
	if r.oneOf(3) {
		max = 1<<32 - 1
		if r.oneOf(2) {
			max = 1<<16 - 1
			if r.oneOf(2) {
				max = 1<<8 - 1
			}
		}
	}
	n := max / elemSize
	delta := uint64(1000 - r.biasedRand(1000, 10))
	if elemSize == 1 || r.oneOf(10) {
		n -= delta
	} else {
		n += delta
	}
	arg.Val = n
	return true
}
