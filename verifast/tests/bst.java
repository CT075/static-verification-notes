
/*@predicate bst(BST t, bintree b)
     requires switch(b) {
       case empty: return t == null;
       case node(bl, a, br):
         return t.value |-> ?v &*& t.left |-> ?l &*& t.right |-> ?r
            &*& bst(l,bl) &*& bst(r,br) &*& t != null &*& a == v;
     } &*& inorder(b) == true;

   inductive bintree = | empty | node(bintree, int, bintree);

   fixpoint int max(bintree b) {
     switch (b) {
       case empty: return 0;
       case node(l,x,r): return r == empty ? x : max(r);
     }
   }

   fixpoint int min(bintree b) {
     switch (b) {
       case empty: return 0;
       case node(l,x,r): return l == empty ? x : min(l);
     }
   }

   fixpoint boolean inorder(bintree b) {
     switch (b) {
       case empty: return true;
       case node(l,x,r):
         return (l == empty || max(l) < x)
             && (r == empty || x < min(r))
             && inorder(l) && inorder(r);
     }
   }

   fixpoint boolean bst_contains(bintree b, int v) {
     switch (b) {
       case empty: return false;
       case node(l, x, r):
         return x == v || (v < x ? bst_contains(l,v) : bst_contains(r,v));
     }
   }

   fixpoint bintree bst_add(bintree b, int v) {
     switch (b) {
       case empty: return node(empty,v,empty);
       case node(l,x,r):
         return v < x ?
           node(bst_add(l,v),x,r) :
           (x == v ?
             node (l,x,r) :
             node (l,x,bst_add(r,v))
           );
     }
   }

   lemma void max_inv_add(bintree l, int v, int x)
     requires v > x &*& (v > max(l) || l == empty) &*& inorder(l) == true;
     ensures v > max(bst_add(l,x)) &*& inorder(l) == true;
   {
     switch(l) {
       case empty:
       case node(l',x',r):
         if (x' > x) {
           max_inv_add(l',x',x);
         }
         if (x > x') {
           max_inv_add(r,v,x);
         }
     }
   }

   lemma void min_inv_add(bintree r, int v, int x)
     requires v < x &*& (v < min(r) || r == empty) &*& inorder(r) == true;
     ensures v < min(bst_add(r,x)) &*& inorder(r)==true;
   {
     switch(r) {
       case empty:
       case node(l,x',r'):
         if (x' < x) {
           min_inv_add(r',x',x);
         }
         if (x < x') {
           min_inv_add(l,v,x);
         }
     }
   }

   lemma void bst_add_inorder(bintree b, int v)
     requires inorder(b) == true &*& bst_contains(b,v) == false;
     ensures
       inorder(bst_add(b,v)) == true &*& bst_contains(bst_add(b,v), v) == true;
   {
     switch (b) {
         case empty:
         case node(l, x, r):
           if (v < x) {
             max_inv_add(l,x,v);
             bst_add_inorder(l,v);
           }
           if (x < v) {
             min_inv_add(r,x,v);
             bst_add_inorder(r,v);
           }
     }
   }
  @*/

class BST {
  public int value;
  public BST left;
  public BST right;

  public BST(int x)
    //@ requires true;
    //@ ensures bst(this, node(empty, x, empty));
  {
    this.value = x;
    this.left = null;
    this.right = null;
    //@ BST l = this.left;
    //@close bst(l, empty);
    //@ BST r = this.right;
    //@close bst(r, empty);
    //@close bst(this, node(empty, x, empty));
  }

  public boolean contains(int x)
    //@requires bst(this, ?b);
    //@ensures bst(this, b) &*& result == bst_contains(b, x);
  {
    if (this == null) {
      //@open bst(this, b);
      //@close bst(this, empty);
      return false;
    }
    else {
      //@open bst(this, b);
      int v = this.value;
      BST l = this.left;
      BST r = this.right;
      if (v == x) {
        //@close bst(this, b);
        return true;
      }
      else {
        if (x < v) {
          boolean inleft = false;

          if (l != null) {
            inleft = l.contains(x);
          }
          else {
            //@open bst(l, ?lv);
            //@close bst(l, lv);
          }
          //@close bst(this, b);
          return inleft;
        }
        else {
          boolean inright = false;
          if (r != null) {
            inright = r.contains(x);
          }
          else {
            //@open bst(r, ?rv);
            //@close bst(r, rv);
          }
          //@close bst(this, b);
          return inright;
        }
      }
    }
  }

  public void add(int x)
    /*@requires
             bst(this, ?b) &*& b != empty
         &*& bst_contains(b, x) == false
         &*& inorder(b) == true;
      @*/
    //@ensures bst(this, bst_add(b,x)) &*& inorder(bst_add(b,x)) == true;
  {
    //@open bst(this, b);
    int v = this.value;
    BST l = this.left;
    //@open bst(l, ?bl);
    //@close bst(l, bl);
    BST r = this.right;
    //@open bst(r, ?br);
    //@close bst(r, br);
    if (x < v) {
      if (l != null) {
        l.add(x);
        //@ bst_add_inorder(b,x);
        //@close bst(this, node(bst_add(bl,x), v, br));
      }
      else {
        BST temp = new BST(x);
        this.left = temp;
        //@open bst(l,bl);
        //@close bst(this, node(node(empty,x,empty), v, br));
        //@ bst_add_inorder(b,x);
      }
    }
    else {
      if (v < x) {
        if (r != null) {
          r.add(x);
          //@ bst_add_inorder(b,x);
          //@close bst(this,node(bl, v, bst_add(br,x)));
        }
        else {
          BST temp = new BST(x);
          this.right = temp;
          //@open bst(r,br);
          //@close bst(this,node(bl, v, node(empty,x,empty)));
        }
      }
    }
  }

  public static void main(String[] args)
    //@requires true;
    //@ensures true;
  {
    BST t1 = null;
    BST t2 = null;

    boolean b = false;

    t1 = new BST(3);

    b = t1.contains(3);
    assert(b);
    b = !t1.contains(3);
    assert(!b);
  }
}

