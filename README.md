# AutomataLean
This project aims to formalize Automata Theory in Lean4. Some parts of Automata Theory have been already formalized in [Mathlib.Computability](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/DFA.html). This project aims to expand on the same, prove some important results regarding PDAs and CFGs, and potentially implement parsing algorithms for CFGs.

## Introduction
**Automata Theory** is a fundamental area of theoretical computer science that focuses on the study of abstract computational models, known as automata, and the formal languages they recognize. It provides a mathematical framework for understanding the behavior of computational systems and the limits of what can be computed.

**Parsers** are fundamental components in compiler design and formal language processing. They analyze sequences of input tokens to determine their syntactic structure based on a **context-free grammar (CFG)**. The output is typically a **parse tree** or **syntax tree**, which represents the hierarchical structure of the input.

Parsing plays a crucial role in verifying the correctness of source code and enabling subsequent stages of compilation. Beyond compilers, parsers are also used in natural language processing and data format validation. Their design is grounded in formal language theory and automata theory, particularly through the use of context-free grammars and pushdown automata.

## Plans
The project aims to address the following goals:

### Primary Goals
- Implement [Pushdown Automata](https://en.wikipedia.org/wiki/Pushdown_automaton) (PDAs) (and maybe [DPDAs](https://en.wikipedia.org/wiki/Deterministic_pushdown_automaton))
- Prove equivalence of acceptance by final state and acceptance by empty stack
- Prove the equivalence of PDAs and [Context-Free Grammars](https://en.wikipedia.org/wiki/Context-free_grammar) (CFGs)
- (Major Theorem) Prove the [Pumping Lemma for Context-Free Languages](https://en.wikipedia.org/wiki/Pumping_lemma_for_context-free_languages) (CFLs)

### Ambitious Goals
- Define parsing trees
- Implement parsing of Context-Free Grammars using a parsing algorithm like [CYK parser](https://en.wikipedia.org/wiki/CYK_algorithm) or [Earley parser](https://en.wikipedia.org/wiki/Earley_parser).
- More, if time permits

## Git Repository
The project repository will be maintained on Github at [https://github.com/NaveenMaurya749/AutomataLean](https://github.com/NaveenMaurya749/AutomataLean)

### Structure of the Repository
The major files of the repository are structured as follows:

```
AutomataLean/           -- repository
├── AutomataLean/       -- main folder containing source code
│ ├── Basic.lean        -- basic macros for proofwriting
│ ├── PDAs.lean         -- pushdown automata (defn, properties, relation to cfgs and cfls, pumping lemma)
│ ├── PDA_testing.lean  -- example of Pushdown Automata (balanced() parentheses())
│ ├── DPDAs.lean        -- deterministic PDAs (abadoned)
│ └── Parsing.lean      -- parse trees (defn), validity, chomsky normal form (cnf), properties
├── AutomataLean.lean   -- root file to be built, imports all modules from AutomataLean/
└── README.md           -- documentation
```
### Import Dependencies
```
AutomataLean.lean
  ├── Basic.lean
  │    └── Lean
  ├── Parsing.lean
  │    └── Mathlib.Computability.ContextFreeGrammar
  ├── PDAs.lean
  │    ├── Mathlib
  │    ├── Basic.lean
  │    └── Parsing.lean 
  └── PDA_testing.lean
       └── PDAs.lean 
```

## References
1. M. Sipser, "Introduction to the Theory of Computation", *Course Technology,* *Boston, MA,* *Third edition,* (*2013*)
2. Hopcroft, Ullman. "Introduction to Automata Theory, Languages and Computation" (*1979*)
3. Various suggestions from indviduals in the Lean Community.
