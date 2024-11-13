// Copyright 2010 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import (
	"go/ast"
	"go/token"
	"reflect"
)

var count struct {
	funcLit             int
	funcLight           int
	singleStatement     int
	longSingleStatement int
	singleReturn        int
	returnVals          [10]int
}

type simplifier struct{}

func (s simplifier) Visit(node ast.Node) ast.Visitor {
	switch n := node.(type) {
	case *ast.CompositeLit:
		// array, slice, and map composite literals may be simplified
		outer := n
		var keyType, eltType ast.Expr
		switch typ := outer.Type.(type) {
		case *ast.ArrayType:
			eltType = typ.Elt
		case *ast.MapType:
			keyType = typ.Key
			eltType = typ.Value
		}

		if eltType != nil {
			var ktyp reflect.Value
			if keyType != nil {
				ktyp = reflect.ValueOf(keyType)
			}
			typ := reflect.ValueOf(eltType)
			for i, x := range outer.Elts {
				px := &outer.Elts[i]
				// look at value of indexed/named elements
				if t, ok := x.(*ast.KeyValueExpr); ok {
					if keyType != nil {
						s.simplifyLiteral(ktyp, keyType, t.Key, &t.Key)
					}
					x = t.Value
					px = &t.Value
				}
				s.simplifyLiteral(typ, eltType, x, px)
			}
			// node was simplified - stop walk (there are no subnodes to simplify)
			return nil
		}

	case *ast.SliceExpr:
		// a slice expression of the form: s[a:len(s)]
		// can be simplified to: s[a:]
		// if s is "simple enough" (for now we only accept identifiers)
		//
		// Note: This may not be correct because len may have been redeclared in
		//       the same package. However, this is extremely unlikely and so far
		//       (April 2022, after years of supporting this rewrite feature)
		//       has never come up, so let's keep it working as is (see also #15153).
		//
		// Also note that this code used to use go/ast's object tracking,
		// which was removed in exchange for go/parser.Mode.SkipObjectResolution.
		// False positives are extremely unlikely as described above,
		// and go/ast's object tracking is incomplete in any case.
		if n.Max != nil {
			// - 3-index slices always require the 2nd and 3rd index
			break
		}
		if s, _ := n.X.(*ast.Ident); s != nil {
			// the array/slice object is a single identifier
			if call, _ := n.High.(*ast.CallExpr); call != nil && len(call.Args) == 1 && !call.Ellipsis.IsValid() {
				// the high expression is a function call with a single argument
				if fun, _ := call.Fun.(*ast.Ident); fun != nil && fun.Name == "len" {
					// the function called is "len"
					if arg, _ := call.Args[0].(*ast.Ident); arg != nil && arg.Name == s.Name {
						// the len argument is the array/slice object
						n.High = nil
					}
				}
			}
		}
		// Note: We could also simplify slice expressions of the form s[0:b] to s[:b]
		//       but we leave them as is since sometimes we want to be very explicit
		//       about the lower bound.
		// An example where the 0 helps:
		//       x, y, z := b[0:2], b[2:4], b[4:6]
		// An example where it does not:
		//       x, y := b[:n], b[n:]

	case *ast.CallExpr:
		// Call/conversion arguments that are ordinary function literals
		// can be simplified to lightweight function literals assuming
		// that the source code typechecks correctly in the first place.
		for i, x := range n.Args {
			if f, _ := x.(*ast.FuncLit); f != nil {
				count.funcLit++
				n.Args[i] = s.simplifyFuncLit(f)
			}
		}

	case *ast.AssignStmt:
		// Ordinary function literals on the LHS of assignments
		// (but not short variable declarations) can be simplified
		// to lightweight function literals assuming that the source
		// code typechecks correctly in the first place.
		for i, x := range n.Rhs {
			f, ok := x.(*ast.FuncLit)
			if !ok {
				continue
			}

			count.funcLit++

			mustHaveNoParams := n.Tok == token.DEFINE
			if i < len(n.Lhs) { // guard against incorrect code
				if v, _ := n.Lhs[i].(*ast.Ident); v != nil && v.Name == "_" {
					mustHaveNoParams = true
				}
			}

			if mustHaveNoParams && len(f.Type.Params.List) != 0 {
				continue
			}

			n.Rhs[i] = s.simplifyFuncLit(f)
		}

	case *ast.RangeStmt:
		// - a range of the form: for x, _ = range v {...}
		// can be simplified to: for x = range v {...}
		// - a range of the form: for _ = range v {...}
		// can be simplified to: for range v {...}
		if isBlank(n.Value) {
			n.Value = nil
		}
		if isBlank(n.Key) && n.Value == nil {
			n.Key = nil
		}
	}

	return s
}

func (s simplifier) simplifyFuncLit(f *ast.FuncLit) ast.Expr {
	if f.Type == nil {
		return f
	}

	// Do not simplify any func()
	if len(f.Type.Params.List) == 0 && (f.Type.Results == nil || len(f.Type.Results.List) == 0) {
		return f
	}

	// Simplification is not possible if the result parameters are named
	// as they may be used in the function body. We don't check for that.
	if f.Type.Results != nil {
		for _, field := range f.Type.Results.List {
			for _, ident := range field.Names {
				if ident.Name != "_" {
					return f
				}
			}
		}
	}

	var params []*ast.Ident
	for _, field := range f.Type.Params.List {
		params = append(params, field.Names...)
	}

	fl := &ast.FuncLight{
		Func: f.Type.Pos(), Lbrace: f.Type.Pos() + 2,
		Params: params, Sep: f.Body.Lbrace,
		Body: f.Body.List, Rbrace: f.Body.Rbrace,
	}

	count.funcLight++

	if len(fl.Body) == 1 {
		count.singleStatement++

		long := int(fl.Body[0].End()-fl.Body[0].Pos())+1 >= 100
		if long {
			count.longSingleStatement++
		}

		if ret, _ := fl.Body[0].(*ast.ReturnStmt); ret != nil {
			count.singleReturn++

			n := len(ret.Results)
			if n >= len(count.returnVals) {
				n = len(count.returnVals) - 1
			}

			if *simplifySingleReturn && !long {
				fl.Body[0] = &ast.ExprStmt{X: ast.ExprList(ret.Results)}
			}

			count.returnVals[n]++
		}
	}

	return fl
}

func (s simplifier) simplifyLiteral(typ reflect.Value, astType, x ast.Expr, px *ast.Expr) {
	ast.Walk(s, x) // simplify x

	// if the element is a composite literal and its literal type
	// matches the outer literal's element type exactly, the inner
	// literal type may be omitted
	if inner, ok := x.(*ast.CompositeLit); ok {
		if match(nil, typ, reflect.ValueOf(inner.Type)) {
			inner.Type = nil
		}
	}
	// if the outer literal's element type is a pointer type *T
	// and the element is & of a composite literal of type T,
	// the inner &T may be omitted.
	if ptr, ok := astType.(*ast.StarExpr); ok {
		if addr, ok := x.(*ast.UnaryExpr); ok && addr.Op == token.AND {
			if inner, ok := addr.X.(*ast.CompositeLit); ok {
				if match(nil, reflect.ValueOf(ptr.X), reflect.ValueOf(inner.Type)) {
					inner.Type = nil // drop T
					*px = inner      // drop &
				}
			}
		}
	}
}

func isBlank(x ast.Expr) bool {
	ident, ok := x.(*ast.Ident)
	return ok && ident.Name == "_"
}

func simplify(f *ast.File) {
	// remove empty declarations such as "const ()", etc
	removeEmptyDeclGroups(f)

	var s simplifier
	ast.Walk(s, f)
}

func removeEmptyDeclGroups(f *ast.File) {
	i := 0
	for _, d := range f.Decls {
		if g, ok := d.(*ast.GenDecl); !ok || !isEmpty(f, g) {
			f.Decls[i] = d
			i++
		}
	}
	f.Decls = f.Decls[:i]
}

func isEmpty(f *ast.File, g *ast.GenDecl) bool {
	if g.Doc != nil || g.Specs != nil {
		return false
	}

	for _, c := range f.Comments {
		// if there is a comment in the declaration, it is not considered empty
		if g.Pos() <= c.Pos() && c.End() <= g.End() {
			return false
		}
	}

	return true
}
