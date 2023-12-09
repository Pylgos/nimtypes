import unittest

import nimtypes

test "getNimTy":
  macro test(val: typed) =
    let ty = getNimTy(val)
    echo treeRepr ty
  
  type
    MyObj = object of RootObj
      fld: int

  type
    MyEnum = enum
      AA
      BB

  let a = true
  test(a)
  var b: ptr UncheckedArray[int]
  test(b)

  var c: array[33, int]
  test(c)

  let d = MyObj()
  test(d)

  var e: (int, float)
  test(e)

  type E = tuple[x: int, y: string]
  test(E)

  type F = sink E
  test(F)

  type G = distinct string
  test(G)

  type H[T, U] = object
    x: T
    y: U
  var h: H[int, float]
  test(h)

  type I[T] = distinct H[T, int]
  var i: I[int]
  test(i)

  var j: MyEnum
  test(j)

  var k: range[0..123]
  test(k)

  test(Ordinal)

  test(proc(a: int, b: string): char)

  type L = int or (float and not bool)
  test(L)

  type M = concept x
    $x is string
  test(M)

  type N = concept
    proc `$`(x: Self): string
  test(N)

  test(iterable[string])

  test({true, false})

  test(static int)

  test(owned int)

test "toTypedesc":
  macro test1(val: typed): untyped =
    let ty = getNimTy(val)
    echo treeRepr ty
    ty.toTypedesc()

  var a: int
  check test1(a) is int

  macro test2(val: typed): untyped =
    let ty = getNimTy(val)
    echo treeRepr ty
    ty[1].toTypedesc()

  var b: tuple[x: int, y: float]
  check test2(b) is float

  var c: (string, char)
  check test2(c) is char

test "recursive object":
  macro test(val: typed): untyped =
    let ty = getNimTy(val)
    echo treeRepr ty

  type
    A = object
      b: ref B
    B = object
      a: ref A
  
  test(A)

test "static generics":
  macro test(val: typed): untyped =
    let ty = getNimTy(val)
    echo treeRepr ty
  
  type A[x: static int] = object
  var a: A[1]
  test(a)
