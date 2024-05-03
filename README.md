A formal matrix library in Coq, which using nat-indexing-function as model.
We start from vector `vec A n`, to `mat A r c` (which is `vec (vec A c) r`).
This model is simple and easy to understand.
We can easily write definition or proof.
The known difficulty is the rewriting need extra declaration and register work.

The homepage of this project is [FunMatrix](https://zhengpushi.github.io/projects/FunMatrix)

The main feature of this library is: 
* immediately evaluation ability in Coq.
  Thus, we have done following:
  1. avoid opaque proof in a definition, such as lia. But we will use lia in pure proof.
  2. tail recursion.
* type safe of vector and matrix operations.
* Fully support Setoid equal from element to complex structures, such as vector and mantrix.
  Thus, the list equality is "eqlistA Aeq", which "Aeq" is setoid equal of two elements.
  Contrast to "FinMatrix", it is fully Leibniz equal.
  This two style (Setoid equal and Leibniz equal) have its own pros and cons.
  1. Leibniz equal support built-in rewriting, but the element also need leibnize equal.
	 Thus, Q could not be supported.
  2. Setoid equal support any type with a equivalence equal, but need to register Instance 
	 of Proper relation.
* No heavy proof burden of dependent type, respect to "FinMatrix".
