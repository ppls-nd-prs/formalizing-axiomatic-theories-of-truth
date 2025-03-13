# To Do
- [x] FOL-syntax
  - [X] signature: `FirstOrder.Language` from `Mathlib.ModelTheory.Basic`
  - [X] terms: `FirstOrder.Language.Term` from `Mathlib.ModelTheory.Syntax`
  - [X] shift: `FirstOrder.Language.Term.liftAt` from `Mathlib.ModelTheory.Syntax`
  - [X] substitution: `FirstOrder.Language.Term.subst` from `Mathlib.ModelTheory.Syntax`
  - [X] formulas (de bruijn): `FirstOrder.Language.Formula` from `Mathlib.ModelTheory.Syntax`
  - [X] sentences: `FirstOrder.Language.Sentence` from `Mathlib.ModelTheory.Syntax`
- [ ] The languages $\mathcal{L}$ and $\mathcal{L}_T$
  - [ ] Specify the signatures of $\mathcal{L}$:
    - Syntax:   
      - [ ] Predicates: $Variable^1, Constant^1, Closed\\_Term^1, Term^1, Formula^1, Sentence^1$
      - [ ] Function symbols: $num^1, denote^1, neg^1, conj^2, disj^2, cond^2, forall^1, exists^1, subs^3$
    - PA
      - [x] Predicates: $\emptyset$
      - [ ] Terms: $add,mult,succ,null$ 
  - [ ] Specify the signatures of $\mathcal{L}_T$
  - [ ] Implement the homomorphism from $\mathcal{L}_{PA}\to \mathcal{L}_T$
- [ ] Get encoding functions
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
