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
          (elem : Elem l (labelsOf ts)) -> getType ts elem
lookupH _ ((_ .=. v) :> _) Here   = v
lookupH l (_ :> hs) (There th)    = lookupH l hs th

lookupR : (l : lty) -> Record ts -> 
          (elem : Elem l (labelsOf ts)) -> getType ts elem
lookupR l (MkRecord _ fs) elem = lookupH l fs elem

MaybeLkp : DecEq lty => List (lty, Type) -> lty -> Type
MaybeLkp ts l = TypeOrUnit (isElem l (labelsOf ts))
                            (\isE => getType ts isE)

infixr 7 .!.

(.!.) : DecEq lty => Record ts -> (l : lty) -> 
        MaybeLkp ts l
(.!.) {ts} r l = mkTorU (isElem l (labelsOf ts))
                         (\isE => getType ts isE)
                         (\isE => lookupR l r isE)


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



-- *** Example (Remove this before pushing to repo) ***
r1 : Record [("surname", String), ("age", Int)]
r1 = ("surname" .=. "Bond") .*.
     ("age" .=. 30) .*.
     emptyRec

r2 : Record [("surname", String), ("name", String)]
r2 = ("surname" .=. "Bond") .*.
     ("name" .=. "James") .*.
     emptyRec
    
r3 : Record [("name", String), ("code", String)]
r3 = ("name" .=. "James") .*.
     ("code" .=. "007") .*.
     emptyRec
