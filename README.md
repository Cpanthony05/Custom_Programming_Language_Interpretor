Lean4-IMP: A Statically-Typed Language Interpreter

A formal implementation of a programming language interpreter using Lean 4. This project features a custom language with a static type system, big-step operational semantics, and support for complex data structures like lists and functions.
Key Features :

    Static Type Checking: Validates expressions and commands before execution to prevent type errors (e.g., adding an Int to a Bool).

    Big-Step Operational Semantics: Formally defined evaluation rules for arithmetic, boolean, and list expressions.

    Complex Scoping: Implements block scoping with variable shadowing. Variables declared inside a block ({ ... }) are discarded upon exit, while modifications to external variables are preserved.

    Function Support: Includes function declarations with parameters, return types, and a result stack for retrieving return values.

    List Processing: Native support for integer lists with operations like head, append, and nth.

    Robust Error Handling: Detects and reports errors such as DivisionByZero, TypeMismatch, UndeclaredVariable, and IndexOutOfBounds.

Language Specification
Supported Types :

    Tip.Int: Integer values.

    Tip.Bool: Boolean values (True/False).

    Tip.List: Lists of integers.

Syntax Overview

    Arithmetic (AExp): Standard operators (+, -, *, /, %) plus list operations (head, length, nth).

    Boolean (BExp): Logic gates (and, or, not) and comparisons (=, <, <=).

    Lists (LExp): Construction via empty, cons, and append.

    Commands (Com):

        :::= (Declaration & Assignment)

        ::= (Update Assignment)

        ;; (Sequencing)

        ite (If-Then-Else)

        while / for (Loops)

        block (Scoped execution)

Code Example: List Processing

The following example demonstrates declaring a list, iterating through it with a while loop, and calculating the sum, min, max, and range—all while using a scoped block for the loop body.
Lean

def ex_list_processing : Com :=
  "data" :::=l (Tip.List Tip.Int), 
    LExp.cons 15 (LExp.cons 8 (LExp.cons 23 (LExp.empty Tip.Int))) ;;
  "sum" :::= Tip.Int, 0 ;;
  "i" :::= Tip.Int, 0 ;;
  "count" :::= Tip.Int, AExp.length (LExp.var "data") ;;
  
  Com.while ("i" <' "count")
    { -- Scoped Block
     "current" :::= Tip.Int, AExp.nth (LExp.var "data") "i" ;;
     "sum" ::= "sum" +' "current" ;;
     "i" ::= "i" +' 1
    }

How to Run

    Ensure you have Lean 4 installed.

    Open the .lean file in your editor (VS Code recommended).

    Use the #eval command to execute programs. Since the language is formally verified, you must provide "fuel" to ensure the interpreter terminates:

Lean

-- Syntax: eval <fuel> <program> <initial_state>
#eval eval 1000 ex_list_processing initial_state

📂 Project Structure

    src/: Contains the Lean 4 source code including the inductive types for syntax and the evaluation functions.

    docs/: Original technical documentation and user guides (available in Romanian).
