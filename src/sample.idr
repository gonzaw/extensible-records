module sample

import extensible_records
import Data.List

-- All functions must be total
%default total

-- *** Initial records ***

--rTest1 : Record [("age", Int)]
--rTest1 = ("age" .=. 30) .*. emptyRec

--rTest2 : Record [("age", Int), ("surname", String)]
--rTest2 = ("surname" .=. "Bond") .*. rTest1

r1 : Record [("age", Int), ("surname", String)]
r1 = ("surname" .=. "Bond") .*.
     ("age" .=. 30) .*.
     emptyRec

r2 : Record [("name", String), ("surname", String)]
r2 = ("surname" .=. "Bond") .*.
     ("name" .=. "James") .*.
     emptyRec
    
r3 : Record [("code", String), ("name", String)]
r3 = ("name" .=. "James") .*.
     ("code" .=. "007") .*.
     emptyRec
     
-- *** Record Extension ***

rExtended : Record [("age", Int), ("name", String), ("surname", String)]
rExtended = ("name" .=. "James") .*. r1          

-- *** Record Alias ***
       
rAlias1 : Rec [("age", Int), ("name", String), ("surname", String)]
rAlias1 = rExtended

rAlias2 : Rec [("name", String), ("age", Int), ("surname", String)]
rAlias2 = rExtended

rAlias3 : Rec [("surname", String), ("age", Int), ("name", String)]                              
rAlias3 = rExtended
                    
-- *** Record Equality ***

rEq1 : Rec [("name", String), ("code", String)]
rEq1 = ("name" .=. "James") .*.
       ("code" .=. "007") .*.
       emptyRec

rEq2 : Rec [("code", String), ("name", String)]
rEq2 = ("code" .=. "007") .*.
       ("name" .=. "James") .*.
       emptyRec
     
-- *** Lookup ***

r1Surname : String
r1Surname = r1 .!. "surname"
-- "Bond"

r1Age : Int
r1Age = r1 .!. "age"
-- 30


-- *** Append ***
{-
rAppend : Rec [("surname", String), ("age", Int), ("name", String), ("code", String)]
rAppend = r1 .++. r3
-- { "surname" = "Bond", "age" = 30, "name" = "James", "code" = "007" }
-}

-- *** Update ***

rUpdate : Rec [("surname", String), ("age", Int)]
rUpdate = updR "surname" r1 "Dean"
-- { "surname" = "Dean", "age" = 30 }


-- *** Delete ***

rDelete : Rec [("age", Int)]
rDelete = "surname" .//. r1
-- { "age" = 30 }


-- *** Delete Labels ***
{-
rDeleteLabels1 : Rec [("age", Int), ("name", String)]
rDeleteLabels1 = ["surname", "code"] .///. rAppend
-- { "age" = 30, "name" = "James" }

rDeleteLabels2 : Rec [("age", Int), ("name", String)]
rDeleteLabels2 = ["code", "surname"] .///. rAppend
-- { "age" = 30, "name" = "James" }
-}

-- *** Left Union ***
{-
rLeftUnion1 : Rec [("surname", String), ("age", Int), ("name", String), ("code", String)]
rLeftUnion1 = r1 .||. r3
-- { "surname" = "Bond", "age" = 30, "name" = "James", "code" = "007" }

r4 : Rec [("name", String), ("code", String)]
r4 = ("name" .=. "Ronald") .*.
     ("code" .=. "007") .*.
     emptyRec
     
rLeftUnion2 : Rec [("surname", String), ("name", String), ("code", String)]
rLeftUnion2 = r2 .||. r4
-- { "surname" = "Bond", "name" = "James", "code" = "007" }

rLeftUnion3 : Rec [("name", String), ("code", String), ("surname", String)]
rLeftUnion3 = r4 .||. r2
-- { "name" = "Ronald", "code" = "007", "surname" = "Bond" }
-}

-- *** Projection ***

r5 : Rec [("name", String), ("surname", String), ("age", Int), ("code", String), ("supervisor", String)]
r5 = ("name" .=. "James") .*.
     ("surname" .=. "Bond") .*.
     ("age" .=. 30) .*.
     ("code" .=. "007") .*.
     ("supervisor" .=. "M") .*.
     emptyRec
     
rProjectLeft : Rec [("name", String), ("age", Int), ("supervisor", String)]
rProjectLeft = ["name", "supervisor", "age"] .<. r5
-- { "name" = "James", "age" = 30, "supervisor" = "M" }

rProjectRight : Rec [("surname", String), ("code", String)]
rProjectRight = ["name", "supervisor", "age"] .>. r5
-- { "surname" = "Bond", "code" = "007" }
