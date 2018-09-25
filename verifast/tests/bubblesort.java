
/*@fixpoint boolean ge_seg(int v, list<int> vs) {
     switch (vs) {
       case nil: return true;
       case cons(x,xs): return v >= x && ge_seg(v, xs);
     }
   }

   fixpoint boolean le_seg(int v, list<int> vs) {
     switch (vs) {
       case nil: return true;
       case cons(x,xs): return v <= x && le_seg(v, xs);
     }
   }

   fixpoint boolean ge_segs(list<int> a, list<int> b) {
     switch (a) {
       case nil: return true;
       case cons(x,xs): return ge_seg(x, b) && ge_segs(xs, b);
     }
   }

   fixpoint boolean le_segs(list<int> a, list<int> b) {
     switch (a) {
       case nil: return true;
       case cons(x,xs): return le_seg(x, b) && le_segs(xs, b);
     }
   }

   fixpoint boolean is_sorted(list<int> vs) {
     switch (vs) {
       case nil: return true;
       case cons(x,xs): return le_seg(x, xs) && is_sorted(xs);
     }
   }

   fixpoint int max(int a, int b) {
     return a > b ? a : b;
   }

   fixpoint int min(int a, int b) {
     return a < b ? a : b;
   }

   lemma void nil_sorted(list<int> vs)
     requires length(vs) == 0;
     ensures is_sorted(vs) == true;
   {
     switch (vs) {
       case cons(x,xs):
       case nil: is_sorted(vs);
     }
   }

   lemma void singleton_sorted(list<int> vs)
     requires length(vs) == 1;
     ensures is_sorted(vs) == true;
   {
     switch (vs) {
       case nil: return;
       case cons(x, xs): switch(xs) {
         case cons(y,ys):
         case nil: le_seg(x, xs);
       }
     }
   }

   lemma void le_segs_neg(list<int> vs)
     requires true;
     ensures le_segs(vs, nil) == true;
   {
     switch (vs) {
       case nil: le_segs(vs, nil);
       case cons(x,xs): le_segs_neg(xs);
     }
   }

   lemma void ge_append(list<int> vs, int v, int v')
     requires ge_seg(v', vs) == true &*& v' >= v;
     ensures ge_seg(v', append(vs, {v})) == true;
   {
     switch (vs) {
       case nil: ge_seg(v', cons(v, nil));
       case cons(x,xs): ge_append(xs, v, v');
     }
   }

   lemma void ge_append'(list<int> vs, int v, int v')
     requires ge_seg(v, vs) == true &*& v' >= v;
     ensures ge_seg(v', append(vs, {v})) == true;
   {
     switch (vs) {
       case nil: ge_seg(v', cons(v, nil));
       case cons(x,xs): ge_append'(xs, v, v');
     }
   }

   lemma void ge_append_trans(int[] l, int i)
     requires
           l[..i] |-> ?st
       &*& l[i] |-> ?v &*& l[i+1..] |-> cons(?v', ?rst)
       &*& v' >= v
       &*& ge_seg(v', st) == true;
     ensures
           l[..i+1] |-> ?st' &*& l[i+1] |-> v' &*& l[i+2..] |-> rst
       &*& st' == append(st, {v})
       &*& ge_seg(v', st') == true;
   {
     ge_append(st, v, v');
   }

   lemma void ge_extend_trans(int[] l, int i)
     requires
           l[..i] |-> ?st
       &*& l[i] |-> ?v &*& l[i+1..] |-> cons(?v', ?rst)
       &*& v' >= v
       &*& ge_seg(v, st) == true;
     ensures
           l[..i+1] |-> ?st' &*& l[i+1] |-> v' &*& l[i+2..] |-> rst
       &*& st' == append(st, {v})
       &*& ge_seg(v', st') == true;
   {
     ge_append'(st, v, v');
   }

   lemma void ge_segs_shrink(int v, list<int> vs, list<int> target)
     requires ge_segs(target, cons(v, vs)) == true;
     ensures ge_segs(target, vs) == true;
   {
     switch (target) {
       case nil: ge_segs(target, vs);
       case cons(x, xs): ge_segs_shrink(v, vs, xs);
     }
   }

   lemma void ge_segs_extend(list<int> st, int v, list<int> rst)
     requires ge_seg(v, st) == true &*& ge_segs(rst, st) == true;
     ensures ge_segs(cons(v, rst), st) == true;
   {
     switch (st) {
       case nil: ge_segs(cons(v, rst), st);
       case cons(x, xs):
                 ge_segs_shrink(x, xs, rst);
                 ge_segs_extend(xs, v, rst);
     }
   }
  @*/

class BubbleSort {
  public static void sort(int[] l)
    //@requires array_slice(l, 0, l.length, _);
    // need to also show that contains the same elements
    //@ensures l[..] |-> ?elts &*& is_sorted(elts) == true;
  {
    if (l.length == 0) {
      //@assert l[..] |-> ?elts;
      //@ nil_sorted(elts);
      return;
    }
    else if (l.length == 1) {
      //@assert l[..] |-> ?elts;
      //@ singleton_sorted(elts);
      return;
    }
    else {
      //@assert l[..] |-> ?elts;
      //@ le_segs_neg(elts);
      for (int numSorted = 0 ; numSorted < l.length-1 ; numSorted += 1)
        /*@invariant
                 numSorted >= 0 &*& numSorted <= l.length-1
             &*& l[..l.length-numSorted] |-> ?hd
             &*& l[l.length-numSorted..] |-> ?tl
             &*& ge_segs(tl, hd) == true
             &*& is_sorted(tl) == true;
          @*/
      {
        // For some reason, this assert holds here but not outside the loop
        //@assert l.length >= 2;

        for (int i = 0 ; i < l.length-numSorted-1 ; i += 1)
          /*@invariant
                   i <= l.length-numSorted-1
               &*& l[..i] |-> ?st
               &*& l[i] |-> ?v &*& l[i+1..] |-> _
               &*& ge_seg(v, st) == true;
            @*/
        {
          //@assert l[i] |-> v &*& l[i+1] |-> ?v';
          if (l[i] > l[i+1]) {
            int tmp = l[i+1];
            l[i+1] = l[i];
            l[i] = tmp;
            //@assert l[i] |-> v' &*& l[i+1] |-> v;
            //@assert v' < v;
            //@assert ge_seg(v, st) == true;
            //@ ge_append_trans(l, i);
          }
          else {
            //@assert v' >= v;
            //@ ge_extend_trans(l, i);
          }
          //@assert l[i] |-> min(v, v') &*& l[i+1] |-> max(v, v');
        }

        // I got stuck here. The problem seems to be that Verifast can't figure
        // out that we haven't touched any thing in the `tl` section defined
        // in the outer loop invariant, and so it can't prove anything about
        // the tail being greater than the head.
        //
        // I remember being able to prove that the tail is sorted in the
        // general case, but it had a similar issue.

        //@assert l[..l.length-numSorted-1] |-> ?st;
        //@assert l[l.length-numSorted..] |-> tl;
        //@assert l[l.length-numSorted-1] |-> ?v;
        //@assert le_seg(v, tl) == true;
        //@assert ge_seg(v, st) == true;
        //@assert ge_segs(rst, st) == true;
        //@ ge_segs_extend(st, v, rst);
      }
    }
  }
}

