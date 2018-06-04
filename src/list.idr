module Record.List

import Data.List

-- All functions must be total
%default total

-- All definitions and functions are exported
%access public export

-- *** Properties of equality ***

symNot : Not (x = y) -> Not (y = x)
symNot notEqual Refl = notEqual Refl


-- *** Properties of List ***

consNotEqNil : {xs : List t} -> Not (x :: xs = [])
consNotEqNil Refl impossible


-- *** Properties of Elem ***

noEmptyElem : Not (Elem x [])
noEmptyElem Here impossible

noElemInCons : Not (Elem x (y :: ys)) -> Not (Elem x ys)
noElemInCons notElemCons elemTail = notElemCons $ There elemTail

ifNotElemThenNotEqual : Not (Elem x (y :: ys)) -> Not (x = y)
ifNotElemThenNotEqual notElemCons equal = notElemCons $ rewrite equal in Here

ifNotEqualNotElemThenNotInCons : Not (Elem x ys) -> Not (x = y) -> Not (Elem x (y :: ys))
ifNotEqualNotElemThenNotInCons nIsE nEq Here = nEq Refl
ifNotEqualNotElemThenNotInCons nIsE nEq (There th) = nIsE th

ifNotElemThenNotInSwitch : Not (Elem x (y :: ys)) -> Not (Elem y ys) -> Not (Elem y (x :: ys))
ifNotElemThenNotInSwitch notXInCons notYInYs Here = notXInCons Here
ifNotElemThenNotInSwitch notXInCons notYInYs (There there) = notYInYs there

-- *** Predicates over lists ***

-- Represents that every element of the first list fulfills a predicate over the entire second list
data AllOverList : (t -> List u -> Type) -> List t -> List u -> Type where
  AllOverListNil : AllOverList p [] us
  AllOverListCons : (v : t) -> p v us -> AllOverList p ts us -> AllOverList p (v :: ts) us

-- All elements from the first list belong in the second list  
AllInList : List t -> List t -> Type
AllInList ts us = AllOverList Elem ts us

-- No element from the first list belong in the second list
AllNotInList : List t -> List t -> Type
AllNotInList ts us = AllOverList (\x => \xs => Not (Elem x xs)) ts us

nothingIsInEmpty : (xs : List t) -> AllNotInList xs []
nothingIsInEmpty [] = AllOverListNil
nothingIsInEmpty (x :: xs) = AllOverListCons x noEmptyElem (nothingIsInEmpty xs)

ifAllNotInConsThenAllNotInRest : AllNotInList ls (x :: xs) -> AllNotInList ls xs
ifAllNotInConsThenAllNotInRest  AllOverListNil = AllOverListNil
ifAllNotInConsThenAllNotInRest {ls = l :: _} (AllOverListCons l nIsE notAllInList) = 
  let allNotInRest = ifAllNotInConsThenAllNotInRest notAllInList
  in AllOverListCons l (noElemInCons nIsE) allNotInRest

ifAllNotInListAndValueNotInFirstOneThenNotInCons : Not (Elem y xs) -> AllNotInList xs ys -> AllNotInList xs (y :: ys)  
ifAllNotInListAndValueNotInFirstOneThenNotInCons nIsE AllOverListNil = AllOverListNil
ifAllNotInListAndValueNotInFirstOneThenNotInCons nIsEY (AllOverListCons x nIsEX allNot) = 
  let allNotInRest = ifAllNotInListAndValueNotInFirstOneThenNotInCons (noElemInCons nIsEY) allNot
      nEq = ifNotElemThenNotEqual nIsEY
      nIsEXCons = ifNotEqualNotElemThenNotInCons nIsEX (symNot nEq)
  in AllOverListCons x nIsEXCons allNotInRest
  
ifAllNotInListThenOthersAreNotInFirstOne : AllNotInList xs ys -> AllNotInList ys xs
ifAllNotInListThenOthersAreNotInFirstOne {ys} AllOverListNil = nothingIsInEmpty ys
ifAllNotInListThenOthersAreNotInFirstOne (AllOverListCons _ nIsE allNot) = 
  let allNotInXs = ifAllNotInListThenOthersAreNotInFirstOne allNot
  in ifAllNotInListAndValueNotInFirstOneThenNotInCons nIsE allNotInXs
  
    
-- *** IsSet ***

data IsSet : List t -> Type where
  IsSetNil : IsSet []
  IsSetCons : Not (Elem x xs) -> IsSet xs -> IsSet (x :: xs)
    
ifSetThenNotElemFirst : IsSet (x :: xs) -> Not (Elem x xs)
ifSetThenNotElemFirst (IsSetCons notXIsInXs  _) = notXIsInXs
  
ifSetThenRestIsSet : IsSet (x :: xs) -> IsSet xs
ifSetThenRestIsSet (IsSetCons _ xsIsSet) = xsIsSet

ifNotSetHereThenNeitherThere : Not (IsSet xs) -> Not (IsSet (x :: xs))
ifNotSetHereThenNeitherThere notXsIsSet (IsSetCons xIsInXs xsIsSet) = notXsIsSet xsIsSet  
  
ifIsElemThenConsIsNotSet : Elem x xs -> Not (IsSet (x :: xs))      
ifIsElemThenConsIsNotSet xIsInXs (IsSetCons notXIsInXs xsIsSet) = notXIsInXs xIsInXs

-- Decidability function for IsSet  
isSet : DecEq t => (xs : List t) -> Dec (IsSet xs)
isSet [] = Yes IsSetNil
isSet (x :: xs) with (isSet xs)
  isSet (x :: xs) | No notXsIsSet = No $ ifNotSetHereThenNeitherThere notXsIsSet
  isSet (x :: xs) | Yes xsIsSet with (isElem x xs)
    isSet (x :: xs) | Yes xsIsSet | No notXInXs = Yes $ IsSetCons notXInXs xsIsSet
    isSet (x :: xs) | Yes xsIsSet | Yes xInXs = No $ ifIsElemThenConsIsNotSet xInXs
    
    
-- *** Functions on List (lty, Type) ***

infixr 2 :##:

-- Ordered insert
(:##:) : Ord lty => (lty, Type) -> List (lty, Type) -> List (lty, Type)
(:##:) x [] = [x]
(:##:) x1@(l1, _) (x2@(l2, _)::xs) = case (compare l1 l2) of
  GT => x2 :: (x1 :##: xs)
  _  => x1 :: x2 :: xs

-- Insert Sort
insort : Ord lty => List (lty, Type) -> List (lty, Type)
insort [] = []
insort (x::xs) = x :##: (insort xs)    
        
labelsOf: List (lty, Type) -> List lty
labelsOf = map fst

infixr 3 ://:

-- Deletes a single element from the list
(://:) : DecEq lty => lty -> List (lty, Type) -> List (lty, Type)
(://:) l [] = []
(://:) l ((l', ty) :: ts) with (decEq l l')
  (://:) l ((l', ty) :: ts) | Yes _ = ts
  (://:) l ((l', ty) :: ts) | No _  = (l', ty) :: (l ://: ts)

infixr 4 :///:
      
-- Deletes a list of elements from the list
(:///:) : DecEq lty => List lty -> List (lty, Type) -> List (lty, Type)
(:///:) [] ts = ts
(:///:) (l :: ls) ts = l ://: (ls :///: ts)

infixr 4 :||:

-- Returns the left union of two lists
(:||:) : DecEq lty => List (lty, Type) -> List (lty, Type) -> List (lty, Type)
(:||:) ts us = ts ++ ((labelsOf ts) :///: us)

infixr 4 :<:

-- Returns left projection of a list
(:<:) : DecEq lty => List lty -> List (lty, Type) -> List (lty, Type)
(:<:) _ [] = []
(:<:) ls ((l, ty) :: ts) with (isElem l ls)
  (:<:) ls ((l, ty) :: ts) | Yes _ = (l, ty) :: (ls :<: ts)
  (:<:) ls ((l, _) :: ts)  | No _  = ls :<: ts

infixr 4 :>:

-- Returns right projection of a lsit
(:>:) : DecEq lty => List lty -> List (lty, Type) -> List (lty, Type)
(:>:) _ [] = []
(:>:) ls ((l, ty) :: ts) with (isElem l ls)
  (:>:) ls ((l, _) :: ts)  | Yes _ = ls :>: ts
  (:>:) ls ((l, ty) :: ts) | No _  = (l, ty) :: (ls :>: ts)

-- *** Theorems on ordered insert ***

ifNotElemThenSoInOrderInsert_Lemma : Not (Elem l1 (l2 :: l3 :: ls)) -> Not (Elem l1 (l3 :: l2 :: ls))
ifNotElemThenSoInOrderInsert_Lemma notElem Here = noElemInCons notElem $ Here
ifNotElemThenSoInOrderInsert_Lemma notElem (There Here) = notElem Here
ifNotElemThenSoInOrderInsert_Lemma notElem (There (There there)) = noElemInCons (noElemInCons notElem) $ there

ifNotElemThenSoInOrderInsert : Ord lty => {l1, l2 : lty} -> Not (Elem l1 (labelsOf ((l2, ty2) :: ls))) ->
  Not (Elem l1 (labelsOf ((l2, ty2) :##: ls)))
ifNotElemThenSoInOrderInsert {ls=[]} notElem elem = notElem elem
ifNotElemThenSoInOrderInsert {l1} {l2} {ty2} {ls=(l3,ty3)::ls} notElem elem with (compare l2 l3)
  ifNotElemThenSoInOrderInsert {l1} {l2} {ty2} {ls=(l3,ty3)::ls} notElem elem | LT = notElem elem
  ifNotElemThenSoInOrderInsert {l1} {l2} {ty2} {ls=(l3,ty3)::ls} notElem elem | EQ = notElem elem
  ifNotElemThenSoInOrderInsert {l1 = l1} {l2 = l2} {ty2 = ty2} {ls=(l1,ty3)::ls} notElem Here | GT = noElemInCons notElem $ Here
  ifNotElemThenSoInOrderInsert {l1 = l1} {l2 = l2} {ty2 = ty2} {ls=(l3,ty3)::ls} notElem (There later) | GT = 
    let notElemL1InSwitch = ifNotElemThenSoInOrderInsert_Lemma notElem
        subPrf = ifNotElemThenSoInOrderInsert {ty2} {ls} $ noElemInCons notElemL1InSwitch
    in subPrf later

ifIsSetThenSoInOrderInsert : Ord lty => {l : lty} -> IsSet (labelsOf ((l, ty) :: ls)) -> IsSet (labelsOf ((l, ty) :##: ls))
ifIsSetThenSoInOrderInsert {ls=[]} isS = isS
ifIsSetThenSoInOrderInsert {l=l1} {ty=ty1} {ls=(l2,ty2)::ls} isS with (compare l1 l2)
  ifIsSetThenSoInOrderInsert {l=l1} {ty=ty1} {ls=(l2,ty2)::ls} isS | LT = isS
  ifIsSetThenSoInOrderInsert {l=l1} {ty=ty1} {ls=(l2,ty2)::ls} isS | EQ = isS
  ifIsSetThenSoInOrderInsert {l=l1} {ty=ty1} {ls=(l2,ty2)::ls} (IsSetCons notL1InL2AndLs (IsSetCons notL2InLs isSLs)) | GT = 
    let notL1InLs = noElemInCons notL1InL2AndLs
        isSL1InLs = IsSetCons notL1InLs isSLs
        isSConsL1ConsLs = ifIsSetThenSoInOrderInsert isSL1InLs
        notL2InL1AndLs = ifNotElemThenNotInSwitch notL1InL2AndLs notL2InLs
        notL2InL1ConsLs = ifNotElemThenSoInOrderInsert notL2InL1AndLs
    in IsSetCons notL2InL1ConsLs isSConsL1ConsLs

-- *** Theorems on append ***

ifIsInOneThenIsInAppend : DecEq lty => {ts, us : List (lty, Type)} -> {l : lty} ->
                          Either (Elem l (labelsOf ts)) (Elem l (labelsOf us)) -> 
                          Elem l (labelsOf (ts ++ us))
ifIsInOneThenIsInAppend (Left isE) = ifIsElemThenIsInAppendLeft isE
  where
    ifIsElemThenIsInAppendLeft : DecEq lty => {ts, us : List (lty, Type)} -> {l : lty} ->
                                 Elem l (labelsOf ts) -> Elem l (labelsOf (ts ++ us))
    ifIsElemThenIsInAppendLeft {ts=((_, _) :: _)} Here = Here
    ifIsElemThenIsInAppendLeft {ts=((_, _) :: _)} (There th) = 
      let isEApp = ifIsElemThenIsInAppendLeft th
      in There isEApp
ifIsInOneThenIsInAppend (Right isE) = ifIsElemThenIsInAppendRight isE   
  where
    ifIsElemThenIsInAppendRight : DecEq lty => {ts, us : List (lty, Type)} -> {l : lty} ->
                                  Elem l (labelsOf us) -> Elem l (labelsOf (ts ++ us))    
    ifIsElemThenIsInAppendRight {ts=[]} isE' = isE'
    ifIsElemThenIsInAppendRight {ts=((_, _) :: _)} {us=[]} isE' = absurd $ noEmptyElem isE'
    ifIsElemThenIsInAppendRight {ts=((_, _) :: _)} {us=((_, _) :: _)} isE' = 
      let isEApp = ifIsElemThenIsInAppendRight isE'
      in There isEApp

ifIsInAppendThenIsInOne : DecEq lty => {ts, us : List (lty, Type)} -> {l : lty} ->
                          Elem l (labelsOf (ts ++ us)) -> 
                          Either (Elem l (labelsOf ts)) (Elem l (labelsOf us))
ifIsInAppendThenIsInOne {ts=[]} isE = Right isE
ifIsInAppendThenIsInOne {ts=((_, _) :: _)} Here = Left Here
ifIsInAppendThenIsInOne {ts=((_, _) :: _)} (There th) =
  case (ifIsInAppendThenIsInOne th) of
    Left isE => Left $ There isE
    Right isE => Right isE
    
ifNotInAppendThenNotInNeither : DecEq lty => {ts, us : List (lty, Type)} -> {l : lty} ->
                                Not (Elem l (labelsOf (ts ++ us))) -> 
                                (Not (Elem l (labelsOf ts)), Not (Elem l (labelsOf us)))
ifNotInAppendThenNotInNeither {ts=[]} {us} {l} notInAppend = (nIsE1, nIsE2)   
  where
    nIsE1 : Not (Elem l [])
    nIsE1 isE = noEmptyElem isE
    
    nIsE2 : Not (Elem l (labelsOf us))
    nIsE2 isE = notInAppend isE    
ifNotInAppendThenNotInNeither {ts=((lt, tyt) :: ts)} {us} {l} nIsEApp = (nIsE1, nIsE2)  
  where    
    nIsE1 : Not (Elem l (labelsOf ((lt, tyt) :: ts)))
    nIsE1 Here impossible
    nIsE1 (There th) = 
      let isEApp = ifIsInOneThenIsInAppend (Left th)
      in nIsEApp (There isEApp)
    
    nIsE2 : Not (Elem l (labelsOf us))
    nIsE2 isE =
      let isEApp = ifIsInOneThenIsInAppend (Right isE)
      in nIsEApp (There isEApp)

ifNotInNeitherThenNotInAppend : DecEq lty => {ts, us : List (lty, Type)} -> {l : lty} ->
                               (Not (Elem l (labelsOf ts)), Not (Elem l (labelsOf us))) -> 
                               Not (Elem l (labelsOf (ts ++ us)))
ifNotInNeitherThenNotInAppend {ts=[]} (_, nIsE2) isEApp = nIsE2 isEApp
ifNotInNeitherThenNotInAppend {ts=((_, _) :: _)} (nIsE1, _) Here = nIsE1 Here
ifNotInNeitherThenNotInAppend {ts=((_, _) :: _)} (nIsE1, nIsE2) (There th) = 
  let nIsEApp = ifNotInNeitherThenNotInAppend ((noElemInCons nIsE1), nIsE2)
  in nIsEApp th

ifAppendIsSetThenEachIsSet : DecEq lty => {ts, us : List (lty, Type)} -> 
                             IsSet (labelsOf (ts ++ us)) -> 
                             (IsSet (labelsOf ts), IsSet (labelsOf us))
ifAppendIsSetThenEachIsSet {ts=[]} isS = (IsSetNil, isS)
ifAppendIsSetThenEachIsSet {ts=((_, _) :: _)} (IsSetCons nIsE isS) =
  let (isSLeft, isSRight) = ifAppendIsSetThenEachIsSet isS
      nIsELeft = fst $ ifNotInAppendThenNotInNeither nIsE
  in (IsSetCons nIsELeft isSLeft, isSRight)

ifEachIsSetThenAppendIsSet : DecEq lty => {ts, us : List (lty, Type)} ->
                             (IsSet (labelsOf ts), IsSet (labelsOf us)) -> AllNotInList (labelsOf ts) (labelsOf us) ->
                             IsSet (labelsOf (ts ++ us))
ifEachIsSetThenAppendIsSet {ts=[]} (_, isSU) AllOverListNil = isSU
ifEachIsSetThenAppendIsSet {ts=(l, _) :: ts} {us} ((IsSetCons nIsET isST), isSU) (AllOverListCons l nIsEU overList) = 
  let isSApp = ifEachIsSetThenAppendIsSet {ts} {us} (isST, isSU) overList
      nIsEApp = ifNotInNeitherThenNotInAppend (nIsET, nIsEU)
  in IsSetCons nIsEApp isSApp
  
  
-- *** Theorems on delete ***

ifDeleteThenIsNotElem : DecEq lty => {ts : List (lty, Type)} -> (l : lty) -> {l' : lty} -> 
                             Not (Elem l' (labelsOf ts)) -> Not (Elem l' (labelsOf (l ://: ts)))
ifDeleteThenIsNotElem {ts=[]} l {l'} nIsE isEDel = absurd $ noEmptyElem isEDel
ifDeleteThenIsNotElem {ts=(l'', ty)::ts} l {l'} nIsE isEDel with (decEq l l'')
  ifDeleteThenIsNotElem {ts=(l, ty)::ts} l {l'} nIsE isEDel      | Yes Refl = (noElemInCons nIsE) isEDel
  ifDeleteThenIsNotElem {ts=(l', ty)::ts} l {l'} nIsE Here       | No contra = nIsE Here
  ifDeleteThenIsNotElem {ts=(l'', ty)::ts} l {l'} nIsE (There th)| No _ = 
                             ifDeleteThenIsNotElem l {l'} {ts} (noElemInCons nIsE) th
  
ifDeleteThenIsSet : DecEq lty => {ts : List (lty, Type)} -> (l : lty) -> IsSet (labelsOf ts) -> IsSet (labelsOf (l ://: ts))
ifDeleteThenIsSet {ts=[]} l isS = IsSetNil
ifDeleteThenIsSet {ts=(l', ty)::ts} l (IsSetCons nIsE isS) with (decEq l l') 
  ifDeleteThenIsSet {ts=(l, ty)::ts} l (IsSetCons nIsE isS)  | Yes Refl = isS
  ifDeleteThenIsSet {ts=(l', ty)::ts} l (IsSetCons nIsE isS) | No _  = 
    let nIsEDel = ifDeleteThenIsNotElem l {l'} nIsE
        isSDel = ifDeleteThenIsSet l isS
    in IsSetCons nIsEDel isSDel
    
    
-- *** Theorems on delete labels ***

ifDeleteLabelsThenIsNotElem : DecEq lty => {ts : List (lty, Type)} -> {l : lty} -> (ls : List lty) -> 
                             Not (Elem l (labelsOf ts)) -> Not (Elem l (labelsOf (ls :///: ts)))
ifDeleteLabelsThenIsNotElem [] nIsE isEDel = absurd $ nIsE isEDel
ifDeleteLabelsThenIsNotElem {ts} {l} (l' :: ls) nIsE isEDel = 
  let nIsEDelLabels = ifDeleteLabelsThenIsNotElem ls {ts} nIsE
  in ifDeleteThenIsNotElem {l'=l} {ts=ls :///: ts} l' nIsEDelLabels isEDel

ifDeleteLabelsThenIsSet : DecEq lty => {ts : List (lty, Type)} -> (ls : List lty) -> IsSet (labelsOf ts) -> IsSet (labelsOf (ls :///: ts))
ifDeleteLabelsThenIsSet [] isS = isS
ifDeleteLabelsThenIsSet (l :: ls) isS = 
  let isSSub = ifDeleteLabelsThenIsSet ls isS 
  in ifDeleteThenIsSet l isSSub

ifDeleteThenResultsAreNotInList : DecEq lty => {ts : List (lty, Type)} -> {ls : List lty} -> (l : lty) ->
  AllNotInList ls (labelsOf ts) -> IsSet (labelsOf ts) ->
  AllNotInList (l :: ls) (labelsOf (l ://: ts))
ifDeleteThenResultsAreNotInList {ts=[]} l overList _ = AllOverListCons l noEmptyElem overList
ifDeleteThenResultsAreNotInList {ts=(l', _) :: ts} l overList isS with (decEq l l')
  ifDeleteThenResultsAreNotInList {ts=(l, _) :: ts} l overList (IsSetCons nIsE _) | Yes Refl =
    let allNotInTs = ifAllNotInConsThenAllNotInRest overList
    in AllOverListCons l nIsE allNotInTs
  ifDeleteThenResultsAreNotInList {ts=(l', _) :: ts} l overList (IsSetCons _ isS) | No nEq = 
    let overRest = ifAllNotInConsThenAllNotInRest overList
        delAreNotInRest = ifDeleteThenResultsAreNotInList {ts} l overRest isS
        (AllOverListCons _ nIsELSupInLs _) = ifAllNotInListThenOthersAreNotInFirstOne overList
        nIsELSupInCons = ifNotEqualNotElemThenNotInCons nIsELSupInLs (symNot nEq)
    in ifAllNotInListAndValueNotInFirstOneThenNotInCons nIsELSupInCons delAreNotInRest  

ifDeleteLabelsThenNoneAreInList : DecEq lty => (ls : List lty) -> (ts : List (lty, Type)) ->
                                  IsSet (labelsOf ts) ->
                                  AllNotInList ls (labelsOf (ls :///: ts))
ifDeleteLabelsThenNoneAreInList [] _ _ = AllOverListNil
ifDeleteLabelsThenNoneAreInList (l :: ls) ts isS = 
  let nInListTs = ifDeleteLabelsThenNoneAreInList ls ts isS
      isSDel = ifDeleteLabelsThenIsSet ls isS
  in ifDeleteThenResultsAreNotInList {ts = ls :///: ts} l nInListTs isSDel
  

-- *** Theorems on left union ***

ifLeftUnionThenIsNotElem : DecEq lty => {ts, us : List (lty, Type)} -> (l : lty) ->
                           Not (Elem l (labelsOf ts)) -> Not (Elem l (labelsOf us)) ->
                           Not (Elem l (labelsOf (ts :||: us)))
ifLeftUnionThenIsNotElem {ts} {us} l nIsET nIsEU = 
  let nIsEDelLabels = ifDeleteLabelsThenIsNotElem {ts=us} (labelsOf ts) nIsEU
      nIsEApp = ifNotInNeitherThenNotInAppend (nIsET, nIsEDelLabels)
  in nIsEApp
  
ifLeftUnionThenisSet : DecEq lty => {ts, us : List (lty, Type)} -> 
                       IsSet (labelsOf ts) -> IsSet (labelsOf us) ->
                       IsSet (labelsOf (ts :||: us))
ifLeftUnionThenisSet {ts} {us} isS1 isS2 = 
  let isSDel = ifDeleteLabelsThenIsSet {ts=us} (labelsOf ts) isS2
      delLabelsNotInList = ifDeleteLabelsThenNoneAreInList (labelsOf ts) us isS2
      isSApp = ifEachIsSetThenAppendIsSet {ts} {us=(labelsOf ts) :///: us} (isS1, isSDel) delLabelsNotInList
  in isSApp 
  
  
-- *** Theorems on left projection ***

ifProjectLeftThenIsNotElem : DecEq lty => {ts : List (lty, Type)} -> (ls : List lty) -> 
                             Not (Elem l (labelsOf ts)) -> Not (Elem l (labelsOf (ls :<: ts)))
ifProjectLeftThenIsNotElem {ts=[]} ls nIsE isEProj = noEmptyElem isEProj
ifProjectLeftThenIsNotElem {ts=(l', _) :: ts} {l} ls nIsE isEProj with (isElem l' ls)
  ifProjectLeftThenIsNotElem {ts=(l, _) :: ts} {l} _ nIsE Here         | Yes _ = nIsE Here
  ifProjectLeftThenIsNotElem {ts=(l', _) :: ts} {l} ls nIsE (There th) | Yes _ = 
    ifProjectLeftThenIsNotElem {ts} ls (noElemInCons nIsE) th
  ifProjectLeftThenIsNotElem {ts=(l', _) :: ts} {l} ls nIsE isEProj    | No _  = 
    ifProjectLeftThenIsNotElem {ts} ls (noElemInCons nIsE) isEProj
    
ifProjectLeftThenIsSet : DecEq lty => {ts : List (lty, Type)} -> (ls : List lty) -> 
                         IsSet (labelsOf ts) -> IsSet (labelsOf (ls :<: ts))
ifProjectLeftThenIsSet {ts=[]} _ _ = IsSetNil
ifProjectLeftThenIsSet {ts=(l, _) :: ts} ls isS with (isElem l ls)
  ifProjectLeftThenIsSet {ts=(l, _) :: ts} ls (IsSetCons nIsE isS) | Yes _ = 
    let nIsEInProj = ifProjectLeftThenIsNotElem {ts} ls nIsE
        isSProj = ifProjectLeftThenIsSet {ts} ls isS
    in IsSetCons nIsEInProj isSProj
  ifProjectLeftThenIsSet {ts=(l, _) :: ts} ls (IsSetCons _ isS)    | No _  = 
                         ifProjectLeftThenIsSet ls isS


-- *** Theorems on right projection ***

ifProjectRightThenIsNotElem : DecEq lty => {ts : List (lty, Type)} -> (ls : List lty) -> 
                             Not (Elem l (labelsOf ts)) -> Not (Elem l (labelsOf (ls :>: ts)))
ifProjectRightThenIsNotElem {ts=[]} ls nIsE isEProj = noEmptyElem isEProj
ifProjectRightThenIsNotElem {ts=(l', _) :: ts} {l} ls nIsE isEProj with (isElem l' ls)
  ifProjectRightThenIsNotElem {ts=(l', _) :: ts} {l} ls nIsE isEProj    | Yes _  = 
    ifProjectRightThenIsNotElem {ts} ls (noElemInCons nIsE) isEProj
  ifProjectRightThenIsNotElem {ts=(l, _) :: ts} {l} _ nIsE Here         | No _ = nIsE Here
  ifProjectRightThenIsNotElem {ts=(l', _) :: ts} {l} ls nIsE (There th) | No _ = 
    ifProjectRightThenIsNotElem {ts} ls (noElemInCons nIsE) th
  
ifProjectRightThenIsSet : DecEq lty => {ts : List (lty, Type)} -> (ls : List lty) -> 
                         IsSet (labelsOf ts) -> IsSet (labelsOf (ls :>: ts))
ifProjectRightThenIsSet {ts=[]} _ _ = IsSetNil
ifProjectRightThenIsSet {ts=(l, _) :: ts} ls isS with (isElem l ls)
  ifProjectRightThenIsSet {ts=(l, _) :: ts} ls (IsSetCons _ isS)    | Yes _ = 
                         ifProjectRightThenIsSet ls isS  
  ifProjectRightThenIsSet {ts=(l, _) :: ts} ls (IsSetCons nIsE isS) | No _ = 
    let nIsEInProj = ifProjectRightThenIsNotElem {ts} ls nIsE
        isSProj = ifProjectRightThenIsSet {ts} ls isS
    in IsSetCons nIsEInProj isSProj
