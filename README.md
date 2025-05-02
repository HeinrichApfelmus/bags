⚗️ EXPERIMENT ⚗️

This repository implements the container type `Bag`
that represents an unordered, finite collection of items.

We are basing the experiment on the article

  * J. Gibbons, F. Henglein, R. Hinze, and N. Wu,
    [Relational algebra by way of adjunctions](https://dl.acm.org/doi/10.1145/3236781),
    Proc. ACM Program. Lang. 2, 1 (2018).

We are interested in formal proofs using [agda2hs](https://github.com/agda/agda2hs).

This is relevant for [Formal Specification of the Cardano Ledger](https://github.com/IntersectMBO/formal-ledger-specifications)
— the idea is to replace the formalization of sets, ℙ,
by a formalization of `Bag`, because that formalization is better behaved under aggregation. See the paper for more details.
