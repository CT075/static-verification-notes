
/* This doesn't actually work yet! Currently needs extra logic to denote that
 * the stack actually pushes new elements onto the top.
 */

class StackNode {
  public int data;
  public StackNode next;
}

/*@predicate stacked(StackNode s, list<int> l, int n) =
     switch(l) {
       case nil: return s == null && n == 0;
       case cons(x, xs):
         return s.data |-> x &*& s.next |-> ?nx &*& stacked(nx, xs, n-1);
     };

   predicate stack(Stack s, int n, list<int> l) =
     s.head |-> ?hd &*& s.len |-> n &*& n >= 0 &*& stacked(hd, l, n);
  @*/

class Stack {
  int len;
  StackNode head;

  public Stack()
    //@requires true;
    //@ensures stack(this, 0, nil);
  {
    this.len = 0;
    this.head = null;
    //@ StackNode hd = this.head;
    //@close stacked(hd, nil, 0);
    //@close stack(this, 0, nil);
  }

  public void push(int i)
    //@requires stack(this, ?n, ?l) &*& n+1 < (1<<31);
    //@ensures stack(this, n+1, cons(i, l));
  {
    //@open stack(this, n, l);
    StackNode nx = new StackNode();
    nx.data = i;
    nx.next = this.head;
    this.len += 1;
    this.head = nx;
    //@close stacked(nx, cons(i,l), n+1);
    //@close stack(this, n+1, cons(i,l));
  }

  public int pop()
    //@requires stack(this, ?n, cons(?x,?xs)) &*& n >= 1;
    //@ensures stack(this, n-1, xs) &*& result == x;
  {
    //@open stack(this, n, cons(x,xs));
    StackNode nxt = this.head;
    //@open stacked(nxt, cons(x,xs), n);
    this.head = nxt.next;
    this.len -= 1;
    //@close stack(this, n-1, xs);
    return nxt.data;
  }

  public int len()
    //@requires stack(this, ?n, ?l);
    //@ensures result == n &*& stack(this, n, l);
  {
    //@open stack(this, n, l);
    int result = len;
    //@close stack(this, n, l);
    return result;
  }

  public int peek()
    /*@requires
         stack(this, ?n, cons(?x,?xs)) &*&
         n >= 1;
      @*/
    //@ensures stack(this, n, cons(x,xs)) &*& result == x;
  {
    //@open stack(this, n, cons(x,xs));
    StackNode nxt = this.head;
    //@open stacked(nxt, cons(x,xs), n);
    int result = nxt.data;
    //@close stacked(nxt, cons(x,xs), n);
    //@close stack(this, n, cons(x,xs));
    return result;
  }
}

class Program {
  public static void main(String[] args)
    //@requires true;
    //@ensures true;
  {
    Stack s = new Stack();

    s.push(5);
    s.push(7);
    int x = s.pop();
    s.push(4);
    s.push(5);

    int y = s.peek() + s.pop() + s.len() + s.pop() + s.pop();

    //@assert x == 7;
    //@assert y == 21;

    boolean b = s.len() == 0;
    assert(b);
  }
}

