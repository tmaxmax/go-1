// Copyright 2024 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package dwarf

import (
	"bytes"
	"flag"
	"fmt"
	"go/ast"
	"go/format"
	"go/parser"
	"go/printer"
	"go/token"
	"os"
	"strconv"
	"strings"
	"testing"
)

const pvagenfile = "./putvarabbrevgen.go"

var pvaDoGenerate bool

func TestMain(m *testing.M) {
	flag.BoolVar(&pvaDoGenerate, "generate", false, "regenerates "+pvagenfile)
	flag.Parse()
	os.Exit(m.Run())

}

// TestPutVarAbbrevGenerator checks that putvarabbrevgen.go is kept in sync
// with the contents of functions putvar and putAbstractVar. If test flag -generate
// is specified the file is regenerated instead.
//
// The block of code in putvar and putAbstractVar that picks the correct
// abbrev is also generated automatically by this function by looking at all
// the possible paths in their CFG and the order in which putattr is called.
//
// There are some restrictions on how putattr can be used in putvar and
// putAbstractVar:
//
//  1. it shouldn't appear inside a for or switch statements
//  2. it can appear within any number of nested if/else statements but the
//     conditionals must not change after putvarAbbrev/putAbstractVarAbbrev
//     are called
//  3. the form argument of putattr must be a compile time constant
//  4. each putattr call must be followed by a comment containing the name of
//     the attribute it is setting
//
// TestPutVarAbbrevGenerator will fail if (1) or (4) are not respected and
// the generated code will not compile if (3) is violated. Violating (2)
// will result in code silently wrong code (which will usually be detected
// by one of the tests that parse debug_info).
func TestPutVarAbbrevGenerator(t *testing.T) {
	spvagenfile := pvagenerate(t)

	if pvaDoGenerate {
		err := os.WriteFile(pvagenfile, []byte(spvagenfile), 0660)
		if err != nil {
			t.Fatal(err)
		}
		return
	}

	slurp := func(name string) string {
		out, err := os.ReadFile(name)
		if err != nil {
			t.Fatal(err)
		}
		return string(out)
	}

	if spvagenfile != slurp(pvagenfile) {
		t.Error(pvagenfile + " is out of date")
	}

}

func pvagenerate(t *testing.T) string {
	var fset token.FileSet
	f, err := parser.ParseFile(&fset, "./dwarf.go", nil, parser.ParseComments)
	if err != nil {
		t.Fatal(err)
	}
	cm := ast.NewCommentMap(&fset, f, f.Comments)
	abbrevs := make(map[string]int)
	funcs := map[string]ast.Stmt{}
	for _, decl := range f.Decls {
		decl, ok := decl.(*ast.FuncDecl)
		if !ok || decl.Body == nil {
			continue
		}
		if decl.Name.Name == "putvar" || decl.Name.Name == "putAbstractVar" {
			// construct the simplified CFG
			pvagraph, _ := pvacfgbody(t, &fset, cm, decl.Body.List)
			funcs[decl.Name.Name+"Abbrev"] = pvacfgvisit(pvagraph, abbrevs)
		}
	}
	abbrevslice := make([]string, len(abbrevs))
	for abbrev, n := range abbrevs {
		abbrevslice[n] = abbrev
	}

	buf := new(bytes.Buffer)
	fmt.Fprint(buf, `// Code generated by TestPutVarAbbrevGenerator. DO NOT EDIT.
// Regenerate using go test -run TestPutVarAbbrevGenerator -generate instead.

package dwarf

var putvarAbbrevs = []dwAbbrev{
`)

	for _, abbrev := range abbrevslice {
		fmt.Fprint(buf, abbrev+",\n")
	}

	fmt.Fprint(buf, "\n}\n\n")

	fmt.Fprint(buf, "func putAbstractVarAbbrev(v *Var) int {\n")
	format.Node(buf, &token.FileSet{}, funcs["putAbstractVarAbbrev"])
	fmt.Fprint(buf, "}\n\n")

	fmt.Fprint(buf, "func putvarAbbrev(v *Var, concrete, withLoclist bool) int {\n")
	format.Node(buf, &token.FileSet{}, funcs["putvarAbbrev"])
	fmt.Fprint(buf, "}\n")

	out, err := format.Source(buf.Bytes())
	if err != nil {
		t.Log(string(buf.Bytes()))
		t.Fatal(err)
	}

	return string(out)
}

type pvacfgnode struct {
	attr, form string

	cond      ast.Expr
	then, els *pvacfgnode
}

// pvacfgbody generates a simplified CFG for a slice of statements,
// containing only calls to putattr and the if statements affecting them.
func pvacfgbody(t *testing.T, fset *token.FileSet, cm ast.CommentMap, body []ast.Stmt) (start, end *pvacfgnode) {
	add := func(n *pvacfgnode) {
		if start == nil || end == nil {
			start = n
			end = n
		} else {
			end.then = n
			end = n
		}
	}
	for _, stmt := range body {
		switch stmt := stmt.(type) {
		case *ast.ExprStmt:
			if x, _ := stmt.X.(*ast.CallExpr); x != nil {
				funstr := exprToString(x.Fun)
				if funstr == "putattr" {
					form, _ := x.Args[3].(*ast.Ident)
					if form == nil {
						t.Fatalf("%s invalid use of putattr", fset.Position(x.Pos()))
					}
					cmt := findLineComment(cm, stmt)
					if cmt == nil {
						t.Fatalf("%s invalid use of putattr (no comment containing the attribute name)", fset.Position(x.Pos()))
					}
					add(&pvacfgnode{attr: strings.TrimSpace(cmt.Text[2:]), form: form.Name})
				}
			}
		case *ast.IfStmt:
			ifStart, ifEnd := pvacfgif(t, fset, cm, stmt)
			if ifStart != nil {
				add(ifStart)
				end = ifEnd
			}
		default:
			// check that nothing under this contains a putattr call
			ast.Inspect(stmt, func { n ->
				if call, _ := n.(*ast.CallExpr); call != nil {
					if exprToString(call.Fun) == "putattr" {
						t.Fatalf("%s use of putattr in unsupported block", fset.Position(call.Pos()))
					}
				}
				return true
			})
		}
	}
	return start, end
}

func pvacfgif(t *testing.T, fset *token.FileSet, cm ast.CommentMap, ifstmt *ast.IfStmt) (start, end *pvacfgnode) {
	thenStart, thenEnd := pvacfgbody(t, fset, cm, ifstmt.Body.List)
	var elseStart, elseEnd *pvacfgnode
	if ifstmt.Else != nil {
		switch els := ifstmt.Else.(type) {
		case *ast.IfStmt:
			elseStart, elseEnd = pvacfgif(t, fset, cm, els)
		case *ast.BlockStmt:
			elseStart, elseEnd = pvacfgbody(t, fset, cm, els.List)
		default:
			t.Fatalf("%s: unexpected statement %T", fset.Position(els.Pos()), els)
		}
	}

	if thenStart != nil && elseStart != nil && thenStart == thenEnd && elseStart == elseEnd && thenStart.form == elseStart.form && thenStart.attr == elseStart.attr {
		return thenStart, thenEnd
	}

	if thenStart != nil || elseStart != nil {
		start = &pvacfgnode{cond: ifstmt.Cond}
		end = &pvacfgnode{}
		if thenStart != nil {
			start.then = thenStart
			thenEnd.then = end
		} else {
			start.then = end
		}
		if elseStart != nil {
			start.els = elseStart
			elseEnd.then = end
		} else {
			start.els = end
		}
	}
	return start, end
}

func exprToString(t ast.Expr) string {
	var buf bytes.Buffer
	printer.Fprint(&buf, token.NewFileSet(), t)
	return buf.String()
}

// findLineComment finds the line comment for statement stmt.
func findLineComment(cm ast.CommentMap, stmt *ast.ExprStmt) *ast.Comment {
	var r *ast.Comment
	for _, cmtg := range cm[stmt] {
		for _, cmt := range cmtg.List {
			if cmt.Slash > stmt.Pos() {
				if r != nil {
					return nil
				}
				r = cmt
			}
		}
	}
	return r
}

// pvacfgvisit visits the CFG depth first, populates abbrevs with all
// possible dwAbbrev definitions and returns a tree of if/else statements
// that picks the correct abbrev.
func pvacfgvisit(pvacfg *pvacfgnode, abbrevs map[string]int) ast.Stmt {
	r := &ast.IfStmt{Cond: &ast.BinaryExpr{
		Op: token.EQL,
		X:  &ast.SelectorExpr{X: &ast.Ident{Name: "v"}, Sel: &ast.Ident{Name: "Tag"}},
		Y:  &ast.Ident{Name: "DW_TAG_variable"}}}
	r.Body = &ast.BlockStmt{List: []ast.Stmt{
		pvacfgvisitnode(pvacfg, "DW_TAG_variable", []*pvacfgnode{}, abbrevs),
	}}
	r.Else = &ast.BlockStmt{List: []ast.Stmt{
		pvacfgvisitnode(pvacfg, "DW_TAG_formal_parameter", []*pvacfgnode{}, abbrevs),
	}}
	return r
}

func pvacfgvisitnode(pvacfg *pvacfgnode, tag string, path []*pvacfgnode, abbrevs map[string]int) ast.Stmt {
	if pvacfg == nil {
		abbrev := toabbrev(tag, path)
		if _, ok := abbrevs[abbrev]; !ok {
			abbrevs[abbrev] = len(abbrevs)
		}
		return &ast.ReturnStmt{
			Results: []ast.Expr{&ast.BinaryExpr{
				Op: token.ADD,
				X:  &ast.Ident{Name: "DW_ABRV_PUTVAR_START"},
				Y:  &ast.BasicLit{Kind: token.INT, Value: strconv.Itoa(abbrevs[abbrev])}}}}
	}
	if pvacfg.attr != "" {
		return pvacfgvisitnode(pvacfg.then, tag, append(path, pvacfg), abbrevs)
	} else if pvacfg.cond != nil {
		if bx, _ := pvacfg.cond.(*ast.BinaryExpr); bx != nil && bx.Op == token.EQL && exprToString(bx.X) == "v.Tag" {
			// this condition is "v.Tag == Xxx", check the value of 'tag'
			y := exprToString(bx.Y)
			if y == tag {
				return pvacfgvisitnode(pvacfg.then, tag, path, abbrevs)
			} else {
				return pvacfgvisitnode(pvacfg.els, tag, path, abbrevs)
			}
		} else {
			r := &ast.IfStmt{Cond: pvacfg.cond}
			r.Body = &ast.BlockStmt{List: []ast.Stmt{pvacfgvisitnode(pvacfg.then, tag, path, abbrevs)}}
			r.Else = &ast.BlockStmt{List: []ast.Stmt{pvacfgvisitnode(pvacfg.els, tag, path, abbrevs)}}
			return r
		}
	} else {
		return pvacfgvisitnode(pvacfg.then, tag, path, abbrevs)
	}
}

func toabbrev(tag string, path []*pvacfgnode) string {
	buf := new(bytes.Buffer)
	fmt.Fprintf(buf, "{\n%s,\nDW_CHILDREN_no,\n[]dwAttrForm{\n", tag)
	for _, node := range path {
		if node.cond == nil {
			fmt.Fprintf(buf, "{%s, %s},\n", node.attr, node.form)

		}
	}
	fmt.Fprint(buf, "},\n}")
	return buf.String()
}
