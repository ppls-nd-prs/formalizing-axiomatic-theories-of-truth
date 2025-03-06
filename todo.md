# To Do
- [ ] FOL-syntax
  - [ ] flypitch
  - [X] signature: `FirstOrder.Language` from `Mathlib.ModelTheory.Basic`
  - [X] terms: `FirstOrder.Language.Term` from `Mathlib.ModelTheory.Syntax`
  - [X] shift: `FirstOrder.Language.Term.liftAt` from `Mathlib.ModelTheory.Syntax`
  - [X] substitution: `FirstOrder.Language.Term.subst` from `Mathlib.ModelTheory.Syntax`
  - [X] formulas (de bruijn): `FirstOrder.Language.Formula` from `Mathlib.ModelTheory.Syntax`
  - [X] sentences: `FirstOrder.Language.Sentence` from `Mathlib.ModelTheory.Syntax`
- [ ] The languages $\mathcal{L}$ and $\mathcal{L}_T$
  - [ ] Specify the signatures of $\mathcal{L}$:
    - Syntax:   
      - [ ] Predicates: $Term,Formula,Sentence$
      - [ ] Function symbols: $num,denote,neg,conj,disj,cond,forall,exists$
    - PA
      - [x] Predicates: $\emptyset$
      - [ ] Terms: $add,mult,succ,null$ 
  - [ ] Specify the signatures of $\mathcal{L}_T$
  - [ ] Implement the homomorphism from $\mathcal{L}_{PA}\to \mathcal{L}_T$
  - [ ] including representation predicates $\texttt{Term, Formula}$ $\dot \land$ etc.
- [ ] Proof theory
  - [ ] Hilbert calculus
    - [X] Theory: `FirstOrder.Language.Theory` from `Mathlib.ModelTheory.Syntax`
    - [ ] modus ponens (MP)
    - [ ] universal generalization ($\forall G$)
    - [ ] Derivations (as a type)
  - [ ] Sequent calculus
    - [X] theory: `FirstOrder.Language.Theory` from `Mathlib.ModelTheory.Syntax`
    - [ ] rules
    - [ ] derivation (as a type)
- [ ] $\texttt{PA}$
  - [ ] proof theory
- [ ] Syntax theory
  - [ ] coding: perhaps we can use the pairwise encoding from FFL
  - [ ] representation
     
# Predicates and Functions To Implement in $\mathcal{L}_{PA}$ and $\mathcal{L}_T$
- [ ] Encoding function to encode an object of the language
- [ ] Decoding function to decode an object of the language
- [ ] Term(n), Formula(n) and Sentence(n) such that e.g. Term(n) holds when n is the code of a term of $\mathcal{L}_{PA}$ and $\mathcal{L}_T$
- [ ] Tr(n) which holds when n is the code of a formula of $\mathcal{L}_{T}$ containing a truth predicate 
- [ ] Dot function which takes each number to its numeral
- [ ] Evaluation function which takes the code of a numeral and spits out the numeral
     
# Planning
| week | Bram | Yu-Lan | Discuss Together |
|---|---|---|---|
| 10 | syntax or concrete  language (check FlyPitch) | figure what predicates | talk about proof theory and derivability |
| 11 | concrete language  | toString function |  |
| 12 | Proof theory | Syntax theory |  |
