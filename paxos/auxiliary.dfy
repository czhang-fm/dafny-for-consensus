module Auxiliary_lemmas {

    /* A few lemmas about finite sets and non-empty sets intersection
     */
    lemma SubsetSize<T> (A1: set<T>, A2: set<T>)
    requires A1 <= A2
    ensures |A1| <= |A2|
    {
        if A1 == {}
        {}
        else {
            var a :| a in A1;
            SubsetSize(A1 - {a}, A2 - {a});
        }
    }
    lemma SizeSubset<T> (A1: set<T>, A2: set<T>)
    requires |A1| > |A2|
    ensures !(A1 <= A2){
        if |A2| == 0 {

        } else {
            var a :| a in A2;
            SizeSubset(A1 - {a}, A2 - {a});
        }
    }
    lemma Intersection<T> (A: set<T>, B: set<T>, C: set<T>)
    requires A <= C && B <= C 
    requires |A| > 0 && |B| > 0
    requires |A| + |B| > |C|
    ensures exists a :: a in A && a in B // && a in C
    {
        SizeSubset(A, C-B);
    }
}