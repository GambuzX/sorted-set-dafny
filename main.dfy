type T = int // example 
class {:autocontracts} BSTNode {
    // Concrete implementation variables.
    var value: T 
    var left: BSTNode?  // elements smaller than 'value' (? - may be null)
    var right: BSTNode? // elements greater than 'value' (? - may be null)

    // Ghost variable used for specification & verification purposes.
    // Holds the set of values in the subtree starting in this node (inclusive). 
    ghost var elems: set<T> 
    ghost var Repr: set<object>

    constructor(x: T) 
        ensures Valid()
        ensures fresh(Repr - {this})
        ensures elems == {x}
    {
        value := x;
        left := null;
        right := null;
        elems := {x};
        Repr := {this};
    }

    // Class invariant with the integrity constraints for the above variables
    predicate Valid() 
        reads this, Repr
    {   
        this in Repr &&

        (left != null ==>
            left in Repr &&
            left.Repr <= Repr && this !in left.Repr &&
            left.Valid() &&
            (forall v :: v in left.elems ==> v < value)) &&

        (right != null ==>
            right in Repr &&
            right.Repr <= Repr && this !in right.Repr &&
            right.Valid() &&
            (forall v :: v in right.elems ==> value < v)) &&

        (left == null && right == null ==>
            elems == {value}) &&

        (left != null && right == null ==>
            elems == left.elems + {value}) &&

        (left == null && right != null ==>
            elems == {value} + right.elems) &&

        (left != null && right != null ==>
            left.Repr !! right.Repr &&
            elems == left.elems + {value} + right.elems)
    }
}

// ordered and no duplicates
class {:autocontracts} TreeSet {

    // Private
    var root: BSTNode? // root of the BST representation, may be null

    // Public
    ghost var elems: set<T>
    ghost var Repr: set<object>

    constructor() 
        ensures elems == {} && Valid()
        ensures fresh(Repr - {this})
    {
        root := null;
        elems := {};
        Repr := {this};
    }

    predicate Valid()
        reads this, Repr
    {
        this in Repr &&
        (root == null ==> elems == {}) &&
        (root != null ==> elems == root.elems &&
                          root in Repr && 
                          root.Repr <= Repr && 
                          this !in root.Repr && 
                          root.Valid())
    }

    method insert(x: T) 
        requires Valid()
        modifies Repr
        ensures Valid()
        ensures fresh(Repr - old(Repr))
        ensures elems == old(elems) + {x}
    {
        var newRoot := insertHelper(x, root);
        root := newRoot;
        elems := root.elems;
        Repr := root.Repr + {this};
    }

    static method insertHelper(x: T, n: BSTNode?) returns (m: BSTNode)
        requires n == null || n.Valid()
        modifies if n != null then n.Repr else {}
        ensures m.Valid()
        ensures n == null ==> fresh(m.Repr) && m.elems == {x}
        ensures n != null ==> m == n && n.elems == old(n.elems) + {x}
        ensures n != null ==> fresh(n.Repr - old(n.Repr))
        decreases if n == null then {} else n.Repr
    {
        if n == null {
            m := new BSTNode(x);
        } else if x == n.value {
            m := n;
        } else {
            if x < n.value {
                assert n.right == null || n.right.Valid();
                var t := insertHelper(x, n.left);
                n.left := t;
                n.Repr := n.Repr + n.left.Repr;
            } else {
                assert n.left == null || n.left.Valid();
                var t := insertHelper(x, n.right);
                n.right := t;
                n.Repr := n.Repr + n.right.Repr;
            }
            n.elems := n.elems + {x};
            m := n;
        }
    }

    /*method delete(x: T) 
    {
        // TODO
    }

    method contains(x: T) returns (res: bool)
    {   
        var result := false;
        if root != null {
            result := root.contains(x);
        }
        return result;
    }

    method asSeq() returns (res: seq<T>)
    {

    }*/
}