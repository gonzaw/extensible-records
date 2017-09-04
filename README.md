# extensible-records
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](https://opensource.org/licenses/MIT)
[![GitHub stars](https://img.shields.io/github/stars/gonzaw/extensible-records.svg)](https://github.com/gonzaw/extensible-records/stargazers)

Extensible records for Idris, using Haskell's [HList](https://hackage.haskell.org/package/HList) as inspiration for its design and API.

## Getting Started

To be able to run this project on your local machine you need to have `Idris` installed. Follow these instructions: https://github.com/idris-lang/Idris-dev/wiki/Installation-Instructions

Afterwards, clone the repository and you can start working on the project.

If you want to load the project into the Idris REPL do the following:

```
idris src/extensible_records.idr
```

If you want to load the samples into the RELP then do:

```
idris src/samples.idr
```

## Usage

To create records you can use the `.*.` operator, ending in a call to the empty record `emptyRec`, like so:

```idris
r1 : Record [("surname", String), ("age", Int)]
r1 = ("surname" .=. "Bond") .*.
     ("age" .=. 30) .*.
     emptyRec
```

To extend a record with new fields, call the `.*.` operator again:

```idris
rExtended : Record [("name", String), ("surname", String), ("age", Int)]
rExtended = ("name" .=. "James") .*. r1
```

### Basic usage of other operators

Beyond record extension, you can manipulate extensible records in many other ways using other operators. Here examples of some operators:

```idris
r2 : Record [("surname", String), ("name", String)]
r2 = ("surname" .=. "Bond") .*.
     ("name" .=. "James") .*.
     emptyRec
    
r3 : Record [("name", String), ("code", String)]
r3 = ("name" .=. "James") .*.
     ("code" .=. "007") .*.
     emptyRec

-- Lookup
r1 .!. "surname"

-- Append
rAppend : Record [("surname", String), ("age", Int), ("name", String), ("code", String)]
rAppend = r1 .++. r3

-- Update
rUpdate : Record [("surname", String), ("age", Int)]
rUpdate = updR "surname" r1 "Dean"

-- Delete
rDelete : Record [("age", Int)]
rDelete = "surname" .//. r1
```

You can find more examples and ways to use such operators in the `samples.idr` file.

## Versioning

We use [SemVer](http://semver.org/) for versioning. For the versions available, see the [tags on this repository](https://github.com/gonzaw/extensible-records/tags). 

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details

## Acknowledgments
Big thank you to my professors Alberto Pardo and Marcos Viera from Universidad de la Republica for helping and guiding me in developing this library for my bacherlor thesis.
Also thank you to the wonderful Idris community who provided helpful advice via IRC.
