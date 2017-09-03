module Record

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

noEmptyElem : Not (Elem x [])
noEmptyElem Here impossible


-- *** Properties of Elem ***

notElemInCons : Not (Elem x (y :: ys)) -> Not (Elem x ys)
notElemInCons notElemCons elemTail = notElemCons $ There elemTail

ifNotElemThenNotEqual : Not (Elem x (y :: ys)) -> Not (x = y)
ifNotElemThenNotEqual notElemCons equal = notElemCons $ rewrite equal in Here

ifNotEqualNotElemThenNotInCons : Not (Elem x ys) -> Not (x = y) -> Not (Elem x (y :: ys))
ifNotEqualNotElemThenNotInCons nIsE nEq Here = nEq Refl
ifNotEqualNotElemThenNotInCons nIsE nEq (There th) = nIsE th

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
  in AllOverListCons l (notElemInCons nIsE) allNotInRest

ifAllNotInListAndValueNotInFirstOneThenNotInCons : Not (Elem y xs) -> AllNotInList xs ys -> AllNotInList xs (y :: ys)  
ifAllNotInListAndValueNotInFirstOneThenNotInCons nIsE AllOverListNil = AllOverListNil
ifAllNotInListAndValueNotInFirstOneThenNotInCons nIsEY (AllOverListCons x nIsEX allNot) = 
  let allNotInRest = ifAllNotInListAndValueNotInFirstOneThenNotInCons (notElemInCons nIsEY) allNot
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
    

-- *** Labelled Heterogeneous List ***    
    
infixr 4 .=.
    
data Field : lty -> Type -> Type where
  (.=.) : (l : lty) -> (v : t) -> Field l t
  
infix 5 :>
  
data LHList : List (lty, Type) -> Type where
  HNil : LHList []
  (:>) : Field lty t -> LHList ts -> LHList ((lty, t) :: ts)

labelsOf: List (lty, Type) -> List lty
labelsOf = map fst

infixr 3 :++:

-- Appends two labelled hlists
(:++:) : LHList ts -> LHList us -> LHList (ts ++ us)
(:++:) HNil ys      = ys
(:++:) (x :> xs) ys = x :> (xs :++: ys)


-- *** Functions on List (lty, Type) ***

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
  let nIsEApp = ifNotInNeitherThenNotInAppend ((notElemInCons nIsE1), nIsE2)
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
  ifDeleteThenIsNotElem {ts=(l, ty)::ts} l {l'} nIsE isEDel      | Yes Refl = (notElemInCons nIsE) isEDel
  ifDeleteThenIsNotElem {ts=(l', ty)::ts} l {l'} nIsE Here       | No contra = nIsE Here
  ifDeleteThenIsNotElem {ts=(l'', ty)::ts} l {l'} nIsE (There th)| No _ = 
                             ifDeleteThenIsNotElem l {l'} {ts} (notElemInCons nIsE) th
  
ifDeleteThenIsSet : DecEq lty => {ts : List (lty, Type)} -> (l : lty) -> IsSet (labelsOf ts) -> IsSet (labelsOf (l ://: ts))
ifDeleteThenIsSet {ts=[]} l isS = IsSetNil
ifDeleteThenIsSet {ts=(l', ty)::ts} l (IsSetCons nIsE isS) with (decEq l l') 
  ifDeleteThenIsSet {ts=(l, ty)::ts} l (IsSetCons nIsE isS) | Yes Refl = isS
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


-- *** Record ***

data Record : List (lty, Type) -> Type where
  MkRecord : IsSet (labelsOf ts) -> LHList ts ->
                                    Record ts
 
recToHList : Record ts -> LHList ts
recToHList (MkRecord _ hs) = hs

recLblIsSet : Record ts -> IsSet (labelsOf ts)
recLblIsSet (MkRecord isS _) = isS

emptyRec : Record []
emptyRec = MkRecord IsSetNil {ts=[]} HNil

hListToRec : DecEq lty => {prf : IsSet (labelsOf ts)} -> LHList ts -> Record ts
hListToRec {prf} hs = MkRecord prf hs


-- *** Automatic generation of proofs ***

TypeOrUnit : Dec p -> (p -> Type) -> Type
TypeOrUnit (Yes yes) tyCons = tyCons yes
TypeOrUnit (No _) _         = ()

mkTorU : (d : Dec p) -> (tyCons : p -> Type) -> 
          (f : (prf : p) -> tyCons prf) ->
          TypeOrUnit d tyCons
mkTorU (Yes yes) _ f = f yes
mkTorU (No _) _ _    = ()

UnitOrType : Dec p -> (Not p -> Type) -> Type
UnitOrType (Yes _) _ = ()
UnitOrType (No no) tyCons = tyCons no

mkUorT : (d : Dec p) -> (tyCons : Not p -> Type) ->
          (f : (contra : Not p) -> tyCons contra) ->
          UnitOrType d tyCons
mkUorT (Yes _) _ _ = ()
mkUorT (No no) _ f = f no

-- TypeOrUnit with constant return type
TypeOrUnitC : Dec p -> Type -> Type
TypeOrUnitC d ty = TypeOrUnit d (\_ => ty)

mkTorUC : (d : Dec p) -> (f : p -> ty)
                     -> TypeOrUnitC d ty
mkTorUC {ty} d f = mkTorU d (\_ => ty)
                       (\p => f p)

-- UnitOrType with constant return type
UnitOrTypeC : Dec p -> Type -> Type
UnitOrTypeC d ty = UnitOrType d (\_ => ty)

mkUorTC : (d : Dec p) -> (f : Not p -> ty)
                     -> UnitOrTypeC d ty
mkUorTC {ty} d f = mkUorT d (\_ => ty)
                       (\np => f np)


-- *** Extension of record ***

consR : DecEq lty => {l : lty} ->
        Field l t -> Record ts ->
        Not (Elem l (labelsOf ts)) ->
        Record ((l, t) :: ts)
consR {ts} f (MkRecord isS fs) notLInTs =
  MkRecord (IsSetCons notLInTs isS) (f :> fs)

MaybeE : DecEq lty => lty -> List (lty, Type) -> Type -> Type
MaybeE l ts r = UnitOrTypeC (isElem l (labelsOf ts)) r

infixr 6 .*.

(.*.) : DecEq lty => {l : lty} ->
        Field l t -> Record ts ->
        MaybeE l ts (Record ((l, t) :: ts))
(.*.) {l} {ts} f r
   = mkUorTC (isElem l (labelsOf ts))
            (\notp => consR f r notp)


-- *** Lookup ***

getType : (ts : List (lty, Type)) -> Elem l (labelsOf ts) -> 
          Type
getType ((l, ty) :: ts) Here      = ty
getType ((l, ty) :: ts)(There th) = getType ts th

lookupH : (l : lty) -> LHList ts -> 
          (isE : Elem l (labelsOf ts)) -> getType ts isE
lookupH _ ((_ .=. v) :> _) Here   = v
lookupH l (_ :> hs) (There th)    = lookupH l hs th

lookupR : (l : lty) -> Record ts -> 
          (isE : Elem l (labelsOf ts)) -> getType ts isE
lookupR l (MkRecord _ fs) isE = lookupH l fs isE

MaybeLkp : DecEq lty => List (lty, Type) -> lty -> Type
MaybeLkp ts l = TypeOrUnit (isElem l (labelsOf ts))
                            (\isE => getType ts isE)

infixr 7 .!.

(.!.) : DecEq lty => Record ts -> (l : lty) -> 
        MaybeLkp ts l
(.!.) {ts} r l = mkTorU (isElem l (labelsOf ts))
                         (\isE => getType ts isE)
                         (\isE => lookupR l r isE)


-- *** Update ***

updateH : DecEq lty => (l : lty) -> 
          (isE : Elem l (labelsOf ts)) -> 
          getType ts isE -> LHList ts -> LHList ts
updateH l {ts=(l,_)::ts} Here v ( _ :> fs) = (l .=. v) :> fs
updateH l {ts=(_,_)::ts} (There th) v (f :> fs) = f :> updateH l th v fs

updateR : DecEq lty => (l : lty) -> 
          (isE : Elem l (labelsOf ts)) -> 
          getType ts isE -> Record ts -> Record ts
updateR l isE v (MkRecord isS fs) = MkRecord isS (updateH l isE v fs)

MaybeUpd : DecEq lty => List (lty, Type) -> lty -> Type
MaybeUpd ts l = TypeOrUnit (isElem l (labelsOf ts))
                (\isE => getType ts isE -> Record ts)

updR : DecEq lty => (l : lty) -> Record ts -> MaybeUpd ts l
updR {ts} l r = 
     mkTorU (isElem l (labelsOf ts))
            (\isE => getType ts isE -> Record ts)
            (\isE => \v => updateR l isE v r)


-- *** Append ***

appendR : DecEq lty => {ts, us : List (lty, Type)} -> 
          Record ts -> Record us ->
          IsSet (labelsOf (ts ++ us)) -> Record (ts ++ us)
appendR (MkRecord _ fs) (MkRecord _ gs) iS = MkRecord iS (fs :++: gs)

MaybeApp : DecEq lty => List (lty, Type) ->
           List (lty, Type) -> Type -> Type
MaybeApp ts us r = 
    TypeOrUnitC (isSet (labelsOf (ts ++ us))) r

infixr 7 .++.

(.++.) : DecEq lty => {ts, us : List (lty, Type)} -> Record ts -> 
         Record us -> MaybeApp ts us (Record (ts ++ us))
(.++.) {ts} {us} rt ru =
       mkTorUC (isSet (labelsOf (ts ++ us)))
               (\p => appendR rt ru p)
            

-- *** Delete ***

hDeleteH : DecEq lty => {ts : List (lty, Type)} -> (l : lty) -> LHList ts -> LHList (l ://: ts)
hDeleteH {ts=[]} _ _ = HNil
hDeleteH {ts=(l', ty)::ts} l (f :> fs) with (decEq l l')
  hDeleteH {ts=(l', ty)::ts} l (f :> fs) | Yes _ = fs
  hDeleteH {ts=(l', ty)::ts} l (f :> fs) | No _  = f :> hDeleteH l fs

infixr 7 .//.

(.//.) : DecEq lty => {ts : List (lty, Type)} -> (l : lty) -> Record ts ->
         Record (l ://: ts)
(.//.) l (MkRecord isS fs) =
  let newFs = hDeleteH l fs
      newIsS = ifDeleteThenIsSet l isS
  in MkRecord newIsS newFs


-- *** Delete Labels ***

hDeleteLabelsH : DecEq lty => {ts : List (lty, Type)} -> (ls : List lty ) -> LHList ts -> LHList (ls :///: ts)
hDeleteLabelsH [] fs = fs
hDeleteLabelsH (l :: ls) fs =  hDeleteH l $ hDeleteLabelsH ls fs
  
infixr 7 .///.

(.///.) : DecEq lty => {ts : List (lty, Type)} -> (ls : List lty) -> Record ts ->
          Record (ls :///: ts)
(.///.) ls (MkRecord isS fs) =
  let newFs = hDeleteLabelsH ls fs
      newIsS = ifDeleteLabelsThenIsSet ls isS
  in MkRecord newIsS newFs


-- *** Left Union ***

hLeftUnionH : DecEq lty => {ts, us : List (lty, Type)} ->
                           LHList ts -> LHList us ->
                           LHList (ts :||: us)
hLeftUnionH {ts} fs gs =  fs :++: (hDeleteLabelsH (labelsOf ts) gs)

infixr 7 .||.

(.||.) : DecEq lty => {ts, us : List (lty, Type)} -> Record ts -> Record us ->
         Record (ts :||: us)
(.||.) (MkRecord isS1 fs) (MkRecord isS2 gs) = 
  let newFs = hLeftUnionH fs gs
      newIsS = ifLeftUnionThenisSet isS1 isS2
  in MkRecord newIsS newFs
