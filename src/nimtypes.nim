import std/[macros, strutils]

type
  NimTyKind* = enum
    tyNone, tyBool, tyChar, tyEmpty,
    tyAlias, tyNil, tyExpr, tyStmt,
    tyTypeDesc, tyGenericInvocation, tyGenericBody, tyGenericInst,
    tyGenericParam, tyDistinct, tyEnum, tyOrdinal,
    tyArray, tyObject, tyTuple, tySet,
    tyRange, tyPtr, tyRef, tyVar,
    tySequence, tyProc, tyPointer, tyOpenArray,
    tyString, tyCString, tyForward, tyInt,
    tyInt8, tyInt16, tyInt32, tyInt64,
    tyFloat, tyFloat32, tyFloat64, tyFloat128,
    tyUInt, tyUInt8, tyUInt16, tyUInt32, tyUInt64,
    tyOwned, tySink, tyLent
    tyVarargs,
    tyUncheckedArray,
    tyError,
    tyBuiltitypeClass, tyUserTypeClass, tyUserTypeClassInst,
    tyCompositeTypeClass, tyInferred, tyAnd, tyOr, tyNot,
    tyAnything, tyStatic, tyFromExpr, tyConcept, tyVoid, tyIterable

  NimTy* = ref object
    ready: bool
    kind: NimTyKind
    typeNode: NimNode
    implNode: NimNode
    rawSons: seq[NimTy]

proc toNimTyKind(kind: NimTypeKind): NimTyKind =
  NimTyKind(int(kind))

proc newNimTy(typeNode: NimNode): NimTy =
  let inst = typeNode.getTypeInst()
  NimTy(
    kind: inst.typeKind.toNimTyKind(),
    typeNode: typeNode,
  )

proc newNimTy(kind: NimTyKind, sons: openArray[NimTy] = [], n: NimNode = nil): NimTy =
  NimTy(
    kind: kind,
    rawSons: @sons,
    implNode: n,
  )

proc skipAlias(n: NimNode): NimNode =
  if n.kind == nnkSym:
    getTypeImpl(n)
  else:
    n

proc prepare(ty: NimTy) =
  if ty == nil: return
  if ty.typeNode == nil: return
  if ty.ready: return
  let inst = ty.typeNode.getTypeInst()
  let skipped = inst.skipAlias()

  case inst.typeKind
  of ntyNone, ntyBool, ntyChar, ntyNil, ntyStmt, ntyVoid, ntyEmpty, ntyPointer, ntyString, ntyCString, ntyInt, ntyInt8, ntyInt16, ntyInt32, ntyInt64,
     ntyUInt, ntyUInt8, ntyUInt16, ntyUInt32, ntyUInt64, ntyFloat, ntyFloat32, ntyFloat64, ntyFloat128,
     ntyError, ntyGenericParam, ntyForward, ntyOrdinal, ntyUserTypeClass, ntyOptDeprecated, ntyStatic:
    discard
  of ntyArray:
    skipped.expectKind nnkBracketExpr
    if inst[1].kind == nnkInfix:
      ty.rawSons.add newNimTy(tyRange, [], nnkRange.newTree(skipped[1][1], skipped[1][2]))
    else:
      ty.rawSons.add newNimTy(skipped[1])
    ty.rawSons.add newNimTy(skipped[2])
  of ntyTypeDesc:
    if inst.kind == nnkBracketExpr:
      ty.rawSons.add newNimTy(skipped[1])
    else:
      ty.rawSons.add newNimTy(tyTypeDesc)
  of ntyGenericInvocation:
    skipped.expectKind nnkBracketExpr
    for n in skipped:
      ty.rawSons.add newNimTy(n)
  of ntyGenericInst:
    for n in skipped:
      ty.rawSons.add newNimTy(n)
  of ntyGenericBody:
    var son: NimTy
    case skipped.kind
    of nnkObjectTy:
      son = newNimTy(tyObject)
      skipped.expectKind nnkObjectTy
      son.implNode = ty.typeNode.getImpl()
      if skipped[1].kind == nnkEmpty:
        son.rawSons.add newNimTy(tyEmpty)
      else:
        skipped[1].expectKind nnkOfInherit
        son.rawSons.add newNimTy(skipped[1][0])
    of nnkDistinctTy:
      son = newNimTy(tyDistinct)
      skipped.expectKind nnkDistinctTy
      son.rawSons.add newNimTy(skipped[0])
    else:
      raiseAssert $skipped.kind
    ty.rawSons.add son
  of ntyObject:
    skipped.expectKind nnkObjectTy
    ty.implNode = ty.typeNode.getImpl()
    if skipped[1].kind == nnkEmpty:
      ty.rawSons.add newNimTy(tyEmpty)
    else:
      skipped[1].expectKind nnkOfInherit
      ty.rawSons.add newNimTy(skipped[1][0])
  of ntyEnum:
    skipped.expectKind nnkEnumTy
    ty.implNode = skipped
  of ntyTuple:
    ty.implNode = skipped
    if skipped.kind == nnkTupleConstr:
      for s in skipped:
        ty.rawSons.add newNimTy(s)
    else:
      skipped.expectKind nnkTupleTy
      for s in skipped:
        s.expectKind nnkIdentDefs
        ty.rawSons.add newNimTy(s[1])
  of ntyPtr, ntyRef, ntyVar:
    ty.rawSons.add newNimTy(skipped[0])
  of ntyUnused0:
    skipped.expectKind nnkBracketExpr
    doAssert skipped[0].strVal == "owned"
    ty.rawSons.add newNimTy(skipped[1])
  of ntyUnused1:
    skipped.expectKind nnkBracketExpr
    doAssert skipped[0].strVal == "sink"
    ty.rawSons.add newNimTy(skipped[1])
  of ntyUnused2:
    skipped.expectKind nnkBracketExpr
    doAssert skipped[0].strVal == "lent"
    ty.rawSons.add newNimTy(skipped[1])
  of ntySequence, ntyOpenArray, ntyUncheckedArray, ntySet, ntyVarargs:
    skipped.expectKind nnkBracketExpr
    ty.rawSons.add newNimTy(skipped[1])
  of ntyDistinct:
    skipped.expectKind nnkDistinctTy
    ty.rawSons.add newNimTy(skipped[0])
  of ntyRange:
    skipped.expectKind nnkBracketExpr
    ty.implNode = skipped[1]
  of ntyProc:
    skipped.expectKind nnkProcTy
    ty.implNode = skipped
    let fp = skipped[0]
    if fp[0].kind == nnkEmpty:
      ty.rawSons.add newNimTy(tyEmpty)
    else:
      ty.rawSons.add newNimTy(fp[0])
    for i in 1..<fp.len:
      ty.rawSons.add newNimTy(fp[i][1])
  of ntyOr, ntyAnd:
    skipped.expectKind nnkBracketExpr
    ty.rawSons.add newNimTy(skipped[1])
    ty.rawSons.add newNimTy(skipped[2])
  of ntyNot:
    skipped.expectKind nnkBracketExpr
    ty.rawSons.add newNimTy(skipped[1])
  elif inst.typeKind.int == 64:
    ty.rawSons.add newNimTy(skipped[1])
  else:
    raiseAssert repr inst.typeKind
  ty.ready = true

proc kind*(nty: NimTy): NimTyKind =
  nty.kind

iterator items*(nty: NimTy): NimTy =
  nty.prepare()
  for n in nty.rawSons:
    n.prepare()
    yield n

proc `[]`*(nty: NimTy, idx: int): NimTy =
  nty.prepare()
  nty.rawSons[idx]

proc `[]`*(nty: NimTy, slice: HSlice): seq[NimTy] =
  nty.prepare()
  nty.rawSons[slice]

proc len*(nty: NimTy): int =
  nty.prepare()
  nty.rawSons.len

proc sameType*(a, b: NimTy): bool =
  sameType(a.typeNode, b.typeNode)

proc sameType*(a: NimTy, b: NimNode): bool =
  sameType(a.typeNode, b)

proc sameType*(a: NimNode, b: NimTy): bool =
  sameType(a, b.typeNode)

proc implNode*(nty: NimTy): NimNode =
  nty.prepare()
  nty.implNode

proc typeNode*(nty: NimTy): NimNode =
  nty.typeNode

proc toTypedesc*(nty: NimTy): NimNode =
  newCall(bindSym"typeof", nty.typeNode)

proc getNimTy*(node: NimNode): NimTy =
  newNimTy(node)

proc treeReprImpl(nty: NimTy, res: var string, depth: int) =
  res.add indent($nty.kind, depth * 2)
  res.add ": "
  res.add nty.implNode.repr.replace("\n", "; ")
  res.add "\n"
  for son in nty:
    treeReprImpl(son, res, depth + 1)

proc treeRepr*(nty: NimTy): string =
  treeReprImpl(nty, result, 0)
