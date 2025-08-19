# ReaderWriterLock-Specification
The repository contains a formal specification of a reader–writer lock written in the Z notation.
The specification is type-checked with Fuzz and then translated to the {log}/SetLog environment to perform satisfiability checks and to generate test cases through the Test Template Framework (TTF).
It includes the document readers-writer-lock-spec.tex, the type-checking output (readers-writer-lock-fuzz-output), scripts and simulations in setlog/, and a report summarizing the work.
