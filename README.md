# Classifying Groups of Order up to 31 in Lean 4

Imperial College London Department of Mathematics Second-year Group Project

The classification of groups of small order up to isomorphism is an important result in group theory that, while heavily cross-checked amongst computer algebra systems, has not yet been formally proven.
Our project addresses this by formalising the classification of groups of order up to~$31$ in the Lean 4 theorem prover.
We have introduced a framework for formalising the classification of finite groups, including a library of concrete groups of small order and formalisations of existing classification theorems.
Using our framework, we prove that every group of order up to~$31$ is isomorphic to exactly one of the~$93$ groups in our library.
We have provided general theorems for the classification of groups of order~$p$,~$p^2$,~$p^3$,~$pq$,~$4q$, and~$2p^2$ for distinct primes~$p$ and~$q$.
In doing this, we have employed novel methodology, leveraging the mathematical reasoning and auto-proving capability of modern large language models.
We expect future efforts in this area to use our general results and expand our library of groups, potentially leading to a fully formalised analogue of the GAP Small Groups Library.
