A formal matrix library in Coq, which using nat-indexing-function as model.
We start from vector `vec A n`, to `mat A r c` (which is `vec (vec A c) r`).
This model is simple and easy to understand.
We can easily write definition or proof.
The known difficulty is the rewriting need extra declaration and register work.

The homepage of this project is [FunMatrix](https://zhengpushi.github.io/projects/FunMatrix)

The main feature of this library is: immediately evaluation ability in Coq.
Thus, we have done following:
1. avoid opaque proof in a definition, such as lia. But we will use lia in pure proof.
2. tail recursion.
