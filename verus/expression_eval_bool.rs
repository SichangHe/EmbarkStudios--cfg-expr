//! Verus proof for the boolean `all`/`any`/`not` postfix reduction used by
//! `Expression::eval`.
//!
//! Rust tests bridge this model to the real public `Expression::parse(...).eval(...)`
//! path on a bounded generated expression set.

use vstd::prelude::*;
use vstd::seq::group_seq_axioms;

fn main() {}

verus! {

enum Model {
    Pred(bool),
    Not(Box<Model>),
    All(Box<Model>),
    Any(Box<Model>),
    Nil,
    Cons(Box<Model>, Box<Model>),
}

enum Node {
    Pred(bool),
    Not,
    All(nat),
    Any(nat),
}

spec fn expr_wf(term: Model) -> bool
    decreases term
{
    match term {
        Model::Pred(_) => true,
        Model::Not(inner) => expr_wf(*inner),
        Model::All(items) => list_wf(*items),
        Model::Any(items) => list_wf(*items),
        _ => false,
    }
}

spec fn list_wf(term: Model) -> bool
    decreases term
{
    match term {
        Model::Nil => true,
        Model::Cons(head, tail) => expr_wf(*head) && list_wf(*tail),
        _ => false,
    }
}

spec fn list_len(list: Model) -> nat
    decreases list
{
    match list {
        Model::Nil => 0,
        Model::Cons(_, tail) => 1 + list_len(*tail),
        _ => 0,
    }
}

spec fn eval_all(values: Seq<bool>) -> bool
    decreases values.len()
{
    if values.len() == 0 {
        true
    } else {
        values[0] && eval_all(values.skip(1))
    }
}

spec fn eval_any(values: Seq<bool>) -> bool
    decreases values.len()
{
    if values.len() == 0 {
        false
    } else {
        values[0] || eval_any(values.skip(1))
    }
}

spec fn values_of_list(list: Model) -> Seq<bool>
    recommends list_wf(list)
    decreases list
{
    match list {
        Model::Nil => Seq::empty(),
        Model::Cons(head, tail) => seq![eval_expr(*head)] + values_of_list(*tail),
        _ => Seq::empty(),
    }
}

spec fn eval_expr(expr: Model) -> bool
    recommends expr_wf(expr)
    decreases expr
{
    match expr {
        Model::Pred(value) => value,
        Model::Not(inner) => !eval_expr(*inner),
        Model::All(items) => eval_all(values_of_list(*items)),
        Model::Any(items) => eval_any(values_of_list(*items)),
        _ => false,
    }
}

spec fn compile_list(list: Model) -> Seq<Node>
    recommends list_wf(list)
    decreases list
{
    match list {
        Model::Nil => Seq::empty(),
        Model::Cons(head, tail) => compile_expr(*head) + compile_list(*tail),
        _ => Seq::empty(),
    }
}

spec fn compile_expr(expr: Model) -> Seq<Node>
    recommends expr_wf(expr)
    decreases expr
{
    match expr {
        Model::Pred(value) => seq![Node::Pred(value)],
        Model::Not(inner) => compile_expr(*inner).push(Node::Not),
        Model::All(items) => compile_list(*items).push(Node::All(list_len(*items))),
        Model::Any(items) => compile_list(*items).push(Node::Any(list_len(*items))),
        _ => Seq::empty(),
    }
}

spec fn reduce_not_stack(stack: Seq<bool>) -> Seq<bool>
    recommends 0 < stack.len()
{
    stack.take(stack.len() as int - 1).push(!stack.last())
}

spec fn reduce_all_stack(stack: Seq<bool>, count: nat) -> Seq<bool>
    recommends count <= stack.len()
{
    stack.take((stack.len() - count) as int).push(eval_all(stack.skip((stack.len() - count) as int)))
}

spec fn reduce_any_stack(stack: Seq<bool>, count: nat) -> Seq<bool>
    recommends count <= stack.len()
{
    stack.take((stack.len() - count) as int).push(eval_any(stack.skip((stack.len() - count) as int)))
}

spec fn eval_postfix(nodes: Seq<Node>, stack: Seq<bool>) -> Seq<bool>
    decreases nodes.len()
{
    if nodes.len() == 0 {
        stack
    } else {
        match nodes[0] {
            Node::Pred(value) => eval_postfix(nodes.skip(1), stack.push(value)),
            Node::Not => eval_postfix(nodes.skip(1), reduce_not_stack(stack)),
            Node::All(count) => eval_postfix(nodes.skip(1), reduce_all_stack(stack, count)),
            Node::Any(count) => eval_postfix(nodes.skip(1), reduce_any_stack(stack, count)),
        }
    }
}

proof fn lemma_list_len_matches_values(list: Model)
    requires
        list_wf(list),
    ensures
        list_len(list) == values_of_list(list).len(),
    decreases list
{
    match list {
        Model::Nil => {}
        Model::Cons(head, tail) => {
            lemma_list_len_matches_values(*tail);
        }
        _ => {}
    }
}

proof fn lemma_reduce_not_push(stack: Seq<bool>, value: bool)
    ensures
        reduce_not_stack(stack.push(value)) =~= stack.push(!value),
{
    broadcast use group_seq_axioms;
}

proof fn lemma_take_prefix(stack: Seq<bool>, values: Seq<bool>)
    ensures
        (stack + values).take(stack.len() as int) =~= stack,
{
    broadcast use group_seq_axioms;
}

proof fn lemma_skip_suffix(stack: Seq<bool>, values: Seq<bool>)
    ensures
        (stack + values).skip(stack.len() as int) =~= values,
{
    broadcast use group_seq_axioms;
}

proof fn lemma_reduce_all_appended(stack: Seq<bool>, values: Seq<bool>)
    ensures
        reduce_all_stack(stack + values, values.len()) =~= stack.push(eval_all(values)),
{
    broadcast use group_seq_axioms;
    lemma_take_prefix(stack, values);
    lemma_skip_suffix(stack, values);
    assert((stack + values).len() - values.len() == stack.len());
}

proof fn lemma_reduce_any_appended(stack: Seq<bool>, values: Seq<bool>)
    ensures
        reduce_any_stack(stack + values, values.len()) =~= stack.push(eval_any(values)),
{
    broadcast use group_seq_axioms;
    lemma_take_prefix(stack, values);
    lemma_skip_suffix(stack, values);
    assert((stack + values).len() - values.len() == stack.len());
}

proof fn lemma_eval_postfix_prefixed_pred(rest: Seq<Node>, stack: Seq<bool>, value: bool)
    ensures
        eval_postfix(seq![Node::Pred(value)] + rest, stack) =~= eval_postfix(rest, stack.push(value)),
{
    broadcast use group_seq_axioms;
    assert((seq![Node::Pred(value)] + rest)[0] == Node::Pred(value));
    assert((seq![Node::Pred(value)] + rest).skip(1) =~= rest);
}

proof fn lemma_eval_postfix_prefixed_not(rest: Seq<Node>, stack: Seq<bool>)
    requires
        0 < stack.len(),
    ensures
        eval_postfix(seq![Node::Not] + rest, stack) =~= eval_postfix(rest, reduce_not_stack(stack)),
{
    broadcast use group_seq_axioms;
    assert((seq![Node::Not] + rest)[0] == Node::Not);
    assert((seq![Node::Not] + rest).skip(1) =~= rest);
}

proof fn lemma_eval_postfix_prefixed_all(rest: Seq<Node>, stack: Seq<bool>, count: nat)
    requires
        count <= stack.len(),
    ensures
        eval_postfix(seq![Node::All(count)] + rest, stack) =~= eval_postfix(rest, reduce_all_stack(stack, count)),
{
    broadcast use group_seq_axioms;
    assert((seq![Node::All(count)] + rest)[0] == Node::All(count));
    assert((seq![Node::All(count)] + rest).skip(1) =~= rest);
}

proof fn lemma_eval_postfix_prefixed_any(rest: Seq<Node>, stack: Seq<bool>, count: nat)
    requires
        count <= stack.len(),
    ensures
        eval_postfix(seq![Node::Any(count)] + rest, stack) =~= eval_postfix(rest, reduce_any_stack(stack, count)),
{
    broadcast use group_seq_axioms;
    assert((seq![Node::Any(count)] + rest)[0] == Node::Any(count));
    assert((seq![Node::Any(count)] + rest).skip(1) =~= rest);
}

proof fn lemma_eval_list_then(stack: Seq<bool>, list: Model, rest: Seq<Node>)
    requires
        list_wf(list),
    ensures
        eval_postfix(compile_list(list) + rest, stack) =~= eval_postfix(rest, stack + values_of_list(list)),
    decreases list
{
    broadcast use group_seq_axioms;

    match list {
        Model::Nil => {
            assert(values_of_list(Model::Nil) =~= Seq::<bool>::empty());
        }
        Model::Cons(head, tail) => {
            assert(compile_list(Model::Cons(head, tail)) + rest =~= compile_expr(*head) + (compile_list(*tail) + rest));
            lemma_eval_expr_then(stack, *head, compile_list(*tail) + rest);
            lemma_eval_list_then(stack.push(eval_expr(*head)), *tail, rest);
            assert(stack.push(eval_expr(*head)) + values_of_list(*tail)
                =~= stack + values_of_list(Model::Cons(head, tail)));
            assert(eval_postfix(compile_list(Model::Cons(head, tail)) + rest, stack)
                =~= eval_postfix(rest, stack + values_of_list(Model::Cons(head, tail)))) by {
                assert(eval_postfix(compile_list(Model::Cons(head, tail)) + rest, stack)
                    =~= eval_postfix(compile_list(*tail) + rest, stack.push(eval_expr(*head))));
                assert(eval_postfix(compile_list(*tail) + rest, stack.push(eval_expr(*head)))
                    =~= eval_postfix(rest, stack.push(eval_expr(*head)) + values_of_list(*tail)));
            }
        }
        _ => {}
    }
}

proof fn lemma_eval_expr_then(stack: Seq<bool>, expr: Model, rest: Seq<Node>)
    requires
        expr_wf(expr),
    ensures
        eval_postfix(compile_expr(expr) + rest, stack) =~= eval_postfix(rest, stack.push(eval_expr(expr))),
    decreases expr
{
    broadcast use group_seq_axioms;

    match expr {
        Model::Pred(value) => {
            lemma_eval_postfix_prefixed_pred(rest, stack, value);
        }
        Model::Not(inner) => {
            assert(compile_expr(Model::Not(inner)) + rest =~= compile_expr(*inner) + (seq![Node::Not] + rest));
            lemma_eval_expr_then(stack, *inner, seq![Node::Not] + rest);
            lemma_eval_postfix_prefixed_not(rest, stack.push(eval_expr(*inner)));
            lemma_reduce_not_push(stack, eval_expr(*inner));
            assert(eval_postfix(compile_expr(Model::Not(inner)) + rest, stack)
                =~= eval_postfix(rest, stack.push(eval_expr(Model::Not(inner))))) by {
                assert(eval_postfix(compile_expr(Model::Not(inner)) + rest, stack)
                    =~= eval_postfix(seq![Node::Not] + rest, stack.push(eval_expr(*inner))));
                assert(eval_postfix(seq![Node::Not] + rest, stack.push(eval_expr(*inner)))
                    =~= eval_postfix(rest, reduce_not_stack(stack.push(eval_expr(*inner)))));
                assert(reduce_not_stack(stack.push(eval_expr(*inner))) =~= stack.push(!eval_expr(*inner)));
            }
        }
        Model::All(items) => {
            lemma_list_len_matches_values(*items);
            assert(compile_expr(Model::All(items)) + rest
                =~= compile_list(*items) + (seq![Node::All(list_len(*items))] + rest));
            lemma_eval_list_then(stack, *items, seq![Node::All(list_len(*items))] + rest);
            lemma_eval_postfix_prefixed_all(rest, stack + values_of_list(*items), list_len(*items));
            lemma_reduce_all_appended(stack, values_of_list(*items));
            assert(eval_postfix(compile_expr(Model::All(items)) + rest, stack)
                =~= eval_postfix(rest, stack.push(eval_expr(Model::All(items))))) by {
                assert(eval_postfix(compile_expr(Model::All(items)) + rest, stack)
                    =~= eval_postfix(seq![Node::All(list_len(*items))] + rest, stack + values_of_list(*items)));
                assert(eval_postfix(seq![Node::All(list_len(*items))] + rest, stack + values_of_list(*items))
                    =~= eval_postfix(rest, reduce_all_stack(stack + values_of_list(*items), list_len(*items))));
                assert(reduce_all_stack(stack + values_of_list(*items), list_len(*items))
                    =~= stack.push(eval_all(values_of_list(*items))));
            }
        }
        Model::Any(items) => {
            lemma_list_len_matches_values(*items);
            assert(compile_expr(Model::Any(items)) + rest
                =~= compile_list(*items) + (seq![Node::Any(list_len(*items))] + rest));
            lemma_eval_list_then(stack, *items, seq![Node::Any(list_len(*items))] + rest);
            lemma_eval_postfix_prefixed_any(rest, stack + values_of_list(*items), list_len(*items));
            lemma_reduce_any_appended(stack, values_of_list(*items));
            assert(eval_postfix(compile_expr(Model::Any(items)) + rest, stack)
                =~= eval_postfix(rest, stack.push(eval_expr(Model::Any(items))))) by {
                assert(eval_postfix(compile_expr(Model::Any(items)) + rest, stack)
                    =~= eval_postfix(seq![Node::Any(list_len(*items))] + rest, stack + values_of_list(*items)));
                assert(eval_postfix(seq![Node::Any(list_len(*items))] + rest, stack + values_of_list(*items))
                    =~= eval_postfix(rest, reduce_any_stack(stack + values_of_list(*items), list_len(*items))));
                assert(reduce_any_stack(stack + values_of_list(*items), list_len(*items))
                    =~= stack.push(eval_any(values_of_list(*items))));
            }
        }
        _ => {}
    }
}

proof fn lemma_eval_expr_append(stack: Seq<bool>, expr: Model)
    requires
        expr_wf(expr),
    ensures
        eval_postfix(compile_expr(expr), stack) =~= stack.push(eval_expr(expr)),
{
    lemma_eval_expr_then(stack, expr, Seq::<Node>::empty());
}

proof fn lemma_compiled_eval_matches_recursive(expr: Model)
    requires
        expr_wf(expr),
    ensures
        eval_postfix(compile_expr(expr), Seq::<bool>::empty()) =~= seq![eval_expr(expr)],
{
    lemma_eval_expr_append(Seq::<bool>::empty(), expr);
}

} // verus!
