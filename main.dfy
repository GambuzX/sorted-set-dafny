// binary tree reference:
// https://github.com/dafny-lang/dafny/blob/master/Test/dafny1/BinaryTree.dfy

type T = int // example 

predicate isSorted(s: seq<T>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate noDuplicates(s: seq<T>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

predicate sameContent(s1: seq<T>, s2: set<T>) {
    (forall i :: 0 <= i < |s1| ==> s1[i] in s2) &&
    (forall i :: i in s2 ==> i in s1) &&
    (|s1| == |s2|)
}

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
    {   
        this in Repr &&

        forall ele :: ele in elems ==> ele == value || (left != null && ele in left.elems) || (right != null && ele in right.elems) &&

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
            elems == {value} && 
            |elems| == 1
        ) &&

        (left != null && right == null ==>
            elems == left.elems + {value} &&
            |elems| == |left.elems| + 1
        ) &&

        (left == null && right != null ==>
            elems == {value} + right.elems &&
            |elems| == |right.elems| + 1
        ) &&

        (left != null && right != null ==>
            left.Repr !! right.Repr &&
            left.elems !! right.elems &&
            elems == left.elems + {value} + right.elems &&
            |elems| == |left.elems| + 1 + |right.elems|
        )
    }

    function method contains(x: T) : bool 
        ensures contains(x) <==> x in elems
        decreases Repr
    {
        if x == value then 
            true
        else if left != null && x < value then 
            left.contains(x)
        else if right != null && x > value then 
            right.contains(x)
        else 
            false
    }

    method delete(x: T) returns (node: BSTNode?)
        modifies Repr
        ensures fresh(Repr - old(Repr))
        ensures node != null ==> node.Valid()
        ensures node == null ==> old(elems) <= {x}
        ensures node != null ==> node.Repr <= Repr && node.elems == old(elems) - {x}
        decreases Repr
    {
        node := this;
        if left != null && x < value {
            var t := left.delete(x);
            left := t;
            elems := elems - {x};
            if left != null { Repr := Repr + left.Repr; }

        } else if right != null && value < x {
            var t := right.delete(x);
            right := t;
            elems := elems - {x};
            if right != null { Repr := Repr + right.Repr; }

        } else if x == value {
            if left == null && right == null {
                node := null;
            } else if left == null {
                node := right;
            } else if right == null {
                node := left;
            } else {
                // rotate
                var min, r := right.deleteMin();
                value := min;  
                right := r;
                elems := elems - {x};
                if right != null {
                    Repr := Repr + right.Repr; 
                }
            }
        }
    }

    method deleteMin() returns (min: T, node: BSTNode?)
        modifies Repr
        ensures fresh(Repr - old(Repr))
        ensures node != null ==> node.Valid()
        ensures node == null ==> old(elems) == {min}
        ensures node != null ==> node.Repr <= Repr && node.elems == old(elems) - {min}
        ensures min in old(elems) && (forall x :: x in old(elems) ==> min <= x)
        decreases Repr
    {
        if left == null {
            min := value;
            node := right;
        } else {
            var t;
            min, t := left.deleteMin();
            left := t;
            node := this;
            elems := elems - {min};
            if left != null { Repr := Repr + left.Repr; }
        }
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
        ensures elems == {}
        ensures fresh(Repr - {this})
    {
        root := null;
        elems := {};
        Repr := {this};
    }

    predicate Valid()
    {
        this in Repr &&
        (root == null ==> elems == {}) &&
        (root != null ==> elems == root.elems &&
                          root in Repr && 
                          root.Repr <= Repr && 
                          this !in root.Repr && 
                          root.Valid())
    }

    function method contains(x: T): bool
        ensures contains(x) <==> x in elems
    {
        root != null && root.contains(x)
    }


    method insert(x: T) 
        modifies Repr
        ensures fresh(Repr - old(Repr))
        ensures elems == old(elems) + {x}
        ensures x in old(elems) ==> elems == old(elems)
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
                var t := insertHelper(x, n.left);
                n.left := t;
                n.Repr := n.Repr + n.left.Repr;
            } else {
                var t := insertHelper(x, n.right);
                n.right := t;
                n.Repr := n.Repr + n.right.Repr;
            }
            n.elems := n.elems + {x};
            m := n;
        }
    }

    method delete(x: T)
        modifies Repr
        ensures fresh(Repr - old(Repr))
        ensures elems == old(elems) - {x}
    {
        if root != null {
            var newRoot := root.delete(x);
            root := newRoot;
            elems := if root == null then {} else root.elems;
            Repr := if root == null then {this} else root.Repr + {this};
        }
    }

    method asSeq() returns (res: seq<T>)
        ensures isSorted(res)
        ensures noDuplicates(res)
        ensures sameContent(res, elems)
    {
        res := asSeqHelper(root);
    }

    static method asSeqHelper(node: BSTNode?) returns (res: seq<T>) 
        requires node == null || node.Valid()
        decreases if node == null then {} else node.Repr
        ensures node == null <==> res == []
        ensures node != null ==> 
            node.Valid() &&
            node.elems == old(node.elems) && 
            node.Repr == old(node.Repr) &&
            node.value == old(node.value) &&
            sameContent(res, node.elems)
        ensures noDuplicates(res)
        ensures isSorted(res)
    {
        if node == null {
            res := [];
        }
        else {
            var leftSeq := asSeqHelper(node.left);
            var rightSeq := asSeqHelper(node.right);   
            res := leftSeq + [node.value] + rightSeq;
        }
    }
}
method testTreeSet() {
    var s := new TreeSet();

    s.insert(12);
    s.insert(24);
    s.insert(1);
    s.insert(1);

    assert s.contains(1) == true;
    assert s.contains(12) == true;
    assert s.contains(24) == true;
    assert s.contains(2) == false;
    assert s.contains(20) == false;

    assert s.contains(64) == false;
    s.insert(64);
    assert s.contains(64) == true;
    ghost var s1 := s.asSeq();
    assert s1 == [1,12,24,64];
    s.delete(64);
    assert s.contains(64) == false;

    ghost var s2 := s.asSeq();
    assert s2 == [1,12,24];
}