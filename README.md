[Proofs Verified with Lean4 (leanprover/lean4:v4.3.0-rc1)](https://github.com/sinhp/LeanHomotopyFrobenius/blob/master/lean-toolchain)

# Lean4 Formalization Of Fibred Categories

This repository is a [Lean 4](https://github.com/leanprover/lean4) formalization of the theory of [Fibred Categories](https://ncatlab.org/nlab/show/Grothendieck+fibration). Fibred categories are one of the most important conceptual toolboxes of category theory and they have many application in category theory, algebraic geometry, categorical logic, and the semantics of programming languages. 

## Content

The project contains

* **The Main Theory** which is being upstreamed to mathlib4: Lemmas that belong in existing mathlib files and background theories. Those are located in the `For_Mathlib` subfolder.

In `Fiber.Lean` we define and provide API for the type of fiber of a functor at a given point in the base. We give an instance of a category structure for this type. We also provide API for the fibre of the opposite functor. 


* **Spec Test Examples**: The formalization in Mathlib is often done at the most level of generality possible. Often it is implicitly assumed that one needs to trust that a formalization of a definition or theorem is correctly specified and does the right thing without inspecting all the hundreds/thousands of definitions and theorems which the theorem of our interest depends on. In this project we do not assume this: For the main theorems of the project, we provide a set of spec-test examples which are meant to be a set of simple examples that the reader can inspect and verify that the formalization does the right thing.

### Spec Test Examples

1. We prove that the codomain functor, defined as below, is a cocartesian fibration. 
    > `def Cod := Arrow.rightFunc (C:= C)`
2. We prove that the domain functor, defined as below, is a cartesian fibration.
    > `def Dom := Arrow.leftFunc (C:= C)`
3. We prove that for a category with finite products, the codomain functor is a cartesian fibration.   
4. Discrete fibrations are another important example of Grothendieck fibrations which are formalized in this project. 
5. We prove that the Grothendieck construction of a `Cat`-valued functor is an example of a cocartesian fibration. In fact this is the archetypal example of a cocartesian fibration.
* **Archived results**: Alternative formalization of certain results which are not upstreamed to mathlib. These results might be useful for other projects, and are kept here for reference. Those are located in the `Archived` subfolder.


### Content under development

The following topics are under active development in `LeanHomotopyFrobenius`.

* Fibred Notion of Structured used to prove the Frobenius Theorem of Homotopy Type Theory in 

> - Sina Hazratpour, Emily Riehl: [*A 2-categorical Proof of Frobenius for Fibrations Defined From a Generic Point*](https://arxiv.org/abs/2210.00078), *Accepted for publication in Mathematical Structures in Computer Science.* 

* The Theory of Street Fibrations 

* Chevalley Characterization of Fibrations and Fibrations Internal to 2-categories

### Resources 
Chapter 2 of my PhD thesis: 
> - [A Logical Study of Some 2-categorical Aspects of Topos Theory, University of Birmingham](https://etheses.bham.ac.uk//id/eprint/9752/7/Hazratpour2019PhD.pdf)



