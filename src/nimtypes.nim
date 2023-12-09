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
    tyUnused0, tySink, tyLent
    tyVarargs,
    tyUncheckedArray,
    tyError,
    tyBuiltitypeClass, tyUserTypeClass, tyUserTypeClassInst,
    tyCompositeTypeClass, tyInferred, tyAnd, tyOr, tyNot,
    tyAnything, tyStatic, tyFromExpr, tyOptDeprecated, tyVoid,

  NimTy* = ref object
    ready: bool
    kind: NimTyKind
    origNode: NimNode
    rawSons: seq[NimTy]
    rawNode: NimNode

proc toNimTyKind(kind: NimTypeKind): NimTyKind =
  NimTyKind(int(kind))

proc newNimTy(origNode: NimNode): NimTy =
  let inst = origNode.getTypeInst()
  NimTy(
    kind: inst.typeKind.toNimTyKind(),
    origNode: origNode,
  )

proc newNimTy(kind: NimTyKind, sons: openArray[NimTy] = [], n: NimNode = nil): NimTy =
  NimTy(
    kind: kind,
    rawSons: @sons,
    rawNode: n,
  )

proc skipAlias(n: NimNode): NimNode =
  if n.kind == nnkSym:
    getTypeImpl(n)
  else:
    n

proc prepare(ty: NimTy) =
  if ty == nil: return
  if ty.origNode == nil: return
  if ty.ready: return
  let inst = ty.origNode.getTypeInst()
  let skipped = inst.skipAlias()
  case inst.typeKind
  of ntyNone, ntyBool, ntyChar, ntyNil, ntyStmt, ntyVoid, ntyEmpty, ntyPointer, ntyString, ntyCString, ntyInt, ntyInt8, ntyInt16, ntyInt32, ntyInt64,
     ntyUInt, ntyUInt8, ntyUInt32, ntyUInt64, ntyFloat, ntyFloat32, ntyFloat64, ntyFloat128,
     ntyError, ntyGenericParam, ntyForward:
    discard
  of ntyUncheckedArray:
    skipped.expectKind nnkBracketExpr
    ty.rawSons.add newNimTy(skipped[1])
  of ntyArray:
    skipped.expectKind nnkBracketExpr
    let t = newNimTy(tyArray)
    if inst[1].kind == nnkInfix:
      t.rawSons.add newNimTy(tyRange, [], nnkRange.newTree(skipped[1][1], skipped[1][2]))
    else:
      t.rawSons.add newNimTy(skipped[1])
    ty.rawSons.add t
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
      son.rawNode = ty.origNode.getImpl()
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
    ty.rawNode = ty.origNode.getImpl()
    if skipped[1].kind == nnkEmpty:
      ty.rawSons.add newNimTy(tyEmpty)
    else:
      skipped[1].expectKind nnkOfInherit
      ty.rawSons.add newNimTy(skipped[1][0])
  of ntyEnum:
    skipped.expectKind nnkEnumTy
    ty.rawNode = skipped
  of ntyTuple:
    ty.rawNode = skipped
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
  of ntyUnused1:
    skipped.expectKind nnkBracketExpr
    doAssert skipped[0].strVal == "sink"
    ty.rawSons.add newNimTy(skipped[1])
  of ntyUnused2:
    skipped.expectKind nnkBracketExpr
    doAssert skipped[0].strVal == "lent"
    ty.rawSons.add newNimTy(skipped[1])
  of ntySequence:
    skipped.expectKind nnkBracketExpr
    ty.rawSons.add newNimTy(skipped[1])
  of ntyDistinct:
    skipped.expectKind nnkDistinctTy
    ty.rawSons.add newNimTy(skipped[0])
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

proc n*(nty: NimTy): NimNode =
  nty.prepare()
  nty.rawNode

proc toTypedesc*(nty: NimTy): NimNode =
  newCall(bindSym"typeof", nty.origNode)

proc getNimTy*(node: NimNode): NimTy =
  newNimTy(node)

proc treeReprImpl(nty: NimTy, res: var string, depth: int) =
  res.add indent($nty.kind, depth * 2)
  res.add ": "
  res.add nty.rawNode.repr.replace("\n", "; ")
  res.add "\n"
  for son in nty:
    treeReprImpl(son, res, depth + 1)

proc treeRepr*(nty: NimTy): string =
  treeReprImpl(nty, result, 0)
