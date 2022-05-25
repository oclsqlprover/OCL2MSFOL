# OCL2MSFOL: A mapping from OCL constraints to Many-sorted First-order Logic

OCL2MSFOL is a _pure_ Java application that generates a Many-Sorted First-Order Logic (MSFOL) theory from an Object Constraint Language (OCL) constraint with an underlying contextual model. The mapping is _strictly_ based on [the work](https://software.imdea.org/~dania/papers/models2016.pdf) of Carolina Dania et. al. at IMDEA Research Institute, Madrid, Spain. The detail of the mapping definition can be reviewed [here](https://software.imdea.org/~dania/tools/definitions.pdf).

OCL works with a four-value logic: _true_, _false_, _null_ and _invalid_. While the first two values are understood universally, 
the last two represent undefinedness: _null_ represents unknown or undefined value whereas _invalid_ represents an error or exception.
Given an OCL constraint (represented as a string) and its contextual model (represented as a JSON file), OCL2MSFOL generates a complete FOL theory in [SMT-LIB2](https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf) language as a text file.

## Supported language and features:

There are four modes that can be chosen from: **TRUE**, **FALSE**, **NULL** and **INVALID**.
Each model corresponds to a different theory which can be interpreted differently. 
For example, given an OCL expression e, using the application with mode **TRUE** generates a MSFOL 
theory that defines scenarios in which evaluating e returns _true_.

Please be aware that neither the mapping definition nor the implementation is complete. 
The following items highlight the supported subset of OCL:

  - literal: Boolean, Integer, String.
    - Boolean: `true`, `false`.
    - Integer: ..., `-1`, `0`, `1`, ...
    - String: `"a string"`, ...
  - predefined variables of permitted types.
    - `caller`, `self`, `user`, ...
  - datamodel's attributes and association-ends.
    - `user.age`, `user.accounts`, ... 
  - datamodel classes's `allInstances()`.
    - `class.allInstances()`
  - logical operations: `not`, `and`, `or`, `implies`.
  - comparison operations `=`, `<`, `<=`, `>`, `>=`, `<>`.
  - collection's operations: `isEmpty()`, `notEmpty()`, `isUnique()`, `forAll()`, `exists()`, `collect()`, `select()`.
  - undefinedness opeartions: `oclIsUndefined()`, `oclIsInvalid()`.

## How to use

### Requirements:
- (required) `Maven 3` and `Java 1.8` (or higher).
- (submodule) [`datamodel`](https://github.com/models22-submission54/dm2schema) - branch: `main`.
- (submodule) [`JavaOCL`](https://github.com/models22-submission54/JavaOCL) - branch: `main`.

The submodules will be automatically install using script commands as JAR files in the guideline.

### Quick guideline:
```
git clone https://github.com/models22-submission54/OCL2MSFOL.git
```
and run the file `scripts.sh` to install the aforementioned packages locally:

```
.\scripts.sh
```
To execute the tool, have a look at the example main class `Runner.java` for a quick guideline.

### Some examples:

Below provides a few OCL expression as examples:

```{java}
//      Case 1: true
        String inv = "true";
        
//      Case 2: caller.students->isEmpty
        OCL2MSFOL.putAdhocContextualSet("caller", "Lecturer");
        String inv = "caller.students->isEmpty()";
        
//      Case 3: self.age >= 18
        OCL2MSFOL.putAdhocContextualSet("self", "Student");
        String inv = "self.age >= 18";
        
//      Case 4: Student.allInstances()->forAll(s|s.lecturers->forAll(l|l.age > s.age))
        String inv = "Student.allInstances()->forAll(s|s.lecturers->forAll(l|l.age > s.age))";

//      Case 5: caller.age = self.age
        OCL2MSFOL.putAdhocContextualSet("self", "Student");
        OCL2MSFOL.putAdhocContextualSet("caller", "Lecturer");
        String inv = "caller.age = self.age";
        
//      Case 6: self.name = user
        OCL2MSFOL.putAdhocContextualSet("self", "Student");
        OCL2MSFOL.putAdhocContextualSet("user", "String");
        String inv = "self.name = user";
```
