module Record

import Data.List
import list

-- All functions must be total
%default total

-- All definitions and functions are exported
%access public export


-- *** Labelled Heterogeneous List ***    
    
infixr 4 .=.
    
data Field : lty -> Type -> Type where
  (.=.) : (l : lty) -> (v : t) -> Field l t
  
infix 5 :>
  
data LHList : List (lty, Type) -> Type where
  HNil : LHList []
  (:>) : Field lty t -> LHList ts -> LHList ((lty, t) :: ts)

infixr 3 :++:

-- Appends two labelled hlists
(:++:) : LHList ts -> LHList us -> LHList (ts ++ us)
(:++:) HNil ys      = ys
(:++:) (x :> xs) ys = x :> (xs :++: ys)


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


-- *** Left Projection ***

projectLeftH : DecEq lty => {ts : List (lty, Type)} -> (ls : List lty) ->
               LHList ts -> LHList (ls :<: ts)
projectLeftH {ts=[]} _ HNil = HNil
projectLeftH {ts=(l, _) :: _} ls fs with (isElem l ls)
  projectLeftH {ts=(l, _) :: _} ls (f :> fs) | Yes _ = f :> projectLeftH ls fs
  projectLeftH {ts=(l, _) :: _} ls (_ :> fs) | No _  = projectLeftH ls fs

infixr 7 .<.

(.<.) : DecEq lty => {ts : List (lty, Type)} -> (ls : List lty) ->
        Record ts -> Record (ls :<: ts)
(.<.) ls (MkRecord isS fs) =
  let newFs = projectLeftH ls fs
      newIsS = ifProjectLeftThenIsSet ls isS
  in MkRecord newIsS newFs


-- *** Right Projection ***

projectRightH : DecEq lty => {ts : List (lty, Type)} -> (ls : List lty) ->
               LHList ts -> LHList (ls :>: ts)
projectRightH {ts=[]} _ HNil = HNil
projectRightH {ts=(l, _) :: _} ls fs with (isElem l ls)
  projectRightH {ts=(l, _) :: _} ls (_ :> fs) | Yes _  = projectRightH ls fs
  projectRightH {ts=(l, _) :: _} ls (f :> fs) | No _ = f :> projectRightH ls fs
  
infixr 7 .>.

(.>.) : DecEq lty => {ts : List (lty, Type)} -> (ls : List lty) ->
        Record ts -> Record (ls :>: ts)
(.>.) ls (MkRecord isS fs) =
  let newFs = projectRightH ls fs
      newIsS = ifProjectRightThenIsSet ls isS
  in MkRecord newIsS newFs
