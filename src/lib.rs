#[macro_use]
extern crate failure;

#[cfg(test)]
#[macro_use]
extern crate matches;

#[macro_use]
extern crate lazy_static;

extern crate serde;
#[macro_use]
extern crate serde_derive;

use std::sync::Arc;

lazy_static! {
    static ref ID_TREE_ZERO: Arc<IdTree> = Arc::new(IdTree::Flag(false));
    static ref ID_TREE_ONE: Arc<IdTree> = Arc::new(IdTree::Flag(true));
    static ref EVENT_TREE_ZERO: Arc<EventTree> = Arc::new(EventTree::Value(0));
}

#[derive(Debug, Fail, PartialEq, Eq, Hash)]
pub enum JoinError {
    #[fail(display = "independent stamps")]
    IndependentStamps,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
enum IdTree {
    Flag(bool),
    Tuple(Arc<IdTree>, Arc<IdTree>),
}

impl IdTree {
    pub fn normalize_in_place(&mut self) {
        use crate::IdTree::*;

        let replace_with = if let Tuple(left, right) = self {
            let left = Arc::make_mut(left);
            left.normalize_in_place();

            let right = Arc::make_mut(right);
            right.normalize_in_place();

            match (left, right) {
                (Flag(false), Flag(false)) => Some(Flag(false)),
                (Flag(true), Flag(true)) => Some(Flag(true)),
                _ => None,
            }
        } else {
            None
        };

        if let Some(replacement) = replace_with {
            *self = replacement;
        }
    }

    pub fn sum(i1: &Self, i2: &IdTree) -> Result<IdTree, JoinError> {
        use crate::IdTree::*;

        match (i1, i2) {
            (Flag(false), i) | (i, Flag(false)) => Ok(i.clone()),
            (Tuple(l1, r1), Tuple(l2, r2)) => {
                let mut result = Tuple(Arc::new(Self::sum(l1, l2)?), Arc::new(Self::sum(r1, r2)?));
                result.normalize_in_place();

                Ok(result)
            }
            (Flag(true), _) | (_, Flag(true)) => Err(JoinError::IndependentStamps),
        }
    }

    pub fn split(&self) -> (IdTree, IdTree) {
        use crate::IdTree::*;

        match self {
            Flag(false) => (Flag(false), Flag(false)),
            Flag(true) => (
                Tuple(ID_TREE_ONE.clone(), ID_TREE_ZERO.clone()),
                Tuple(ID_TREE_ZERO.clone(), ID_TREE_ONE.clone()),
            ),
            Tuple(i1, i2) => {
                if let Flag(false) = **i1 {
                    let (i1, i2) = i2.split();
                    (
                        Tuple(ID_TREE_ZERO.clone(), Arc::new(i1)),
                        Tuple(ID_TREE_ZERO.clone(), Arc::new(i2)),
                    )
                } else if let Flag(false) = **i2 {
                    let (i1, i2) = i1.split();
                    (
                        Tuple(Arc::new(i1), ID_TREE_ZERO.clone()),
                        Tuple(Arc::new(i2), ID_TREE_ZERO.clone()),
                    )
                } else {
                    (
                        Tuple(i1.clone(), ID_TREE_ZERO.clone()),
                        Tuple(ID_TREE_ZERO.clone(), i2.clone()),
                    )
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
enum EventTree {
    Value(u64),
    Tuple(u64, Arc<EventTree>, Arc<EventTree>),
}

impl EventTree {
    fn lift_in_place(&mut self, amount: u64) {
        use crate::EventTree::*;

        match self {
            Value(ref mut value) | Tuple(ref mut value, _, _) => *value = *value + amount,
        }
    }

    fn lower_in_place(&mut self, amount: u64) {
        use crate::EventTree::*;

        match self {
            Value(ref mut value) | Tuple(ref mut value, _, _) => *value = *value - amount,
        }
    }

    fn min_normalized(&self) -> u64 {
        use crate::EventTree::*;

        match self {
            Value(value) | Tuple(value, _, _) => *value,
        }
    }

    fn max(&self) -> u64 {
        use crate::EventTree::*;

        match self {
            Value(value) => *value,
            Tuple(value, left, right) => *value + ::std::cmp::max(left.max(), right.max()),
        }
    }

    pub fn normalize_in_place(&mut self) {
        use crate::EventTree::*;

        let replace_with = if let Tuple(value, left, right) = self {
            let left = Arc::make_mut(left);
            left.normalize_in_place();

            let right = Arc::make_mut(right);
            right.normalize_in_place();

            match (left, right) {
                (Value(left_value), Value(right_value)) if left_value == right_value => {
                    Some(Value(*value + *left_value))
                }
                (left, right) => {
                    let min = ::std::cmp::min(left.min_normalized(), right.min_normalized());

                    left.lower_in_place(min);
                    right.lower_in_place(min);
                    *value += min;
                    None
                }
            }
        } else {
            None
        };

        if let Some(replacement) = replace_with {
            *self = replacement;
        }
    }

    fn less_than_or_equal(&self, e2: &EventTree) -> bool {
        let e1 = self;

        match (e1, e2) {
            (EventTree::Value(n1), EventTree::Value(n2))
            | (EventTree::Value(n1), EventTree::Tuple(n2, _, _)) => n1 <= n2,
            (EventTree::Tuple(n1, l1, r1), EventTree::Value(n2)) => {
                if n1 <= n2 {
                    let mut l1 = (**l1).clone();
                    l1.lift_in_place(*n1);

                    if l1.less_than_or_equal(&EventTree::Value(*n2)) {
                        let mut r1 = (**r1).clone();
                        r1.lift_in_place(*n1);

                        r1.less_than_or_equal(&EventTree::Value(*n2))
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            (EventTree::Tuple(n1, l1, r1), EventTree::Tuple(n2, l2, r2)) => {
                if n1 <= n2 {
                    let mut l1 = (**l1).clone();
                    l1.lift_in_place(*n1);

                    let mut l2 = (**l2).clone();
                    l2.lift_in_place(*n2);

                    if l1.less_than_or_equal(&l2) {
                        let mut r1 = (**r1).clone();
                        r1.lift_in_place(*n1);

                        let mut r2 = (**r2).clone();
                        r2.lift_in_place(*n2);

                        r1.less_than_or_equal(&r2)
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
        }
    }

    pub fn join(e1: &Self, e2: &EventTree) -> EventTree {
        use crate::EventTree::*;

        match (e1, e2) {
            (Value(n1), Value(n2)) => Value(::std::cmp::max(*n1, *n2)),
            (Value(n1), right @ Tuple(_, _, _)) => EventTree::join(
                &Tuple(*n1, EVENT_TREE_ZERO.clone(), EVENT_TREE_ZERO.clone()),
                right,
            ),
            (left @ Tuple(_, _, _), Value(n2)) => EventTree::join(
                left,
                &Tuple(*n2, EVENT_TREE_ZERO.clone(), EVENT_TREE_ZERO.clone()),
            ),
            (Tuple(n1, _, _), Tuple(n2, _, _)) if n1 > n2 => EventTree::join(e2, e1),
            (Tuple(n1, l1, r1), Tuple(n2, l2, r2)) => {
                let mut lifted_l2 = (**l2).clone();
                lifted_l2.lift_in_place(n2 - n1);

                let mut lifted_r2 = (**r2).clone();
                lifted_r2.lift_in_place(n2 - n1);

                let mut result = Tuple(
                    *n1,
                    Arc::new(EventTree::join(l1, &lifted_l2)),
                    Arc::new(EventTree::join(r1, &lifted_r2)),
                );

                result.normalize_in_place();

                result
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Stamp(IdTree, EventTree);

impl Stamp {
    pub fn seed() -> Self {
        Stamp(IdTree::Flag(true), EventTree::Value(0))
    }

    pub fn normalize_in_place(&mut self) {
        let Stamp(i, e) = self;
        i.normalize_in_place();
        e.normalize_in_place();
    }

    pub fn less_than_or_equal(&self, other: &Stamp) -> bool {
        let Stamp(_, e1) = self;
        let Stamp(_, e2) = other;

        e1.less_than_or_equal(e2)
    }

    pub fn fork(&self) -> (Stamp, Stamp) {
        let Stamp(i, e) = self;

        let (i1, i2) = i.split();
        (Stamp(i1, e.clone()), Stamp(i2, e.clone()))
    }

    pub fn join(left: &Self, right: &Stamp) -> Result<Stamp, JoinError> {
        let id_tree = IdTree::sum(&left.0, &right.0)?;
        let event_tree = EventTree::join(&left.1, &right.1);
        Ok(Stamp(id_tree, event_tree))
    }

    pub fn event(&self) -> Stamp {
        let mut cloned = self.clone();
        cloned.fill_in_place();

        if cloned.1 != self.1 {
            cloned
        } else {
            let (e2, _) = self.grow();
            Stamp(cloned.0, e2)
        }
    }

    fn grow(&self) -> (EventTree, (usize, usize)) {
        match self {
            Stamp(IdTree::Flag(true), EventTree::Value(n)) => (EventTree::Value(n + 1), (0, 0)),
            Stamp(i, EventTree::Value(n)) => {
                let (e2, c) = Stamp(
                    i.clone(),
                    EventTree::Tuple(*n, EVENT_TREE_ZERO.clone(), EVENT_TREE_ZERO.clone()),
                ).grow();

                (e2, c)
            }
            Stamp(IdTree::Tuple(il, ir), EventTree::Tuple(n, el, er)) => {
                let il = &**il;
                let ir = &**ir;
                if let IdTree::Flag(false) = il {
                    let (er2, (lc, rc)) = Stamp(ir.clone(), (**er).clone()).grow();
                    (
                        EventTree::Tuple(*n, el.clone(), Arc::new(er2)),
                        (lc, rc + 1),
                    )
                } else if let IdTree::Flag(false) = ir {
                    let (el2, (lc, rc)) = Stamp(il.clone(), (**el).clone()).grow();
                    (
                        EventTree::Tuple(*n, Arc::new(el2), er.clone()),
                        (lc + 1, rc),
                    )
                } else {
                    let (el2, cl) = Stamp(il.clone(), (**el).clone()).grow();
                    let (er2, cr) = Stamp(ir.clone(), (**er).clone()).grow();

                    if cl < cr {
                        (
                            EventTree::Tuple(*n, Arc::new(el2), er.clone()),
                            (cl.0 + 1, cl.1),
                        )
                    } else {
                        (
                            EventTree::Tuple(*n, el.clone(), Arc::new(er2)),
                            (cr.0, cr.1 + 1),
                        )
                    }
                }
            }
            Stamp(IdTree::Flag(false), _) => {
                unreachable!("a stamp will never have an id tree of zero")
            }
            Stamp(IdTree::Flag(true), EventTree::Tuple(_, _, _)) => {
                unreachable!("a stamp will never have a single id but a tuple event tree")
            }
        }
    }

    fn fill_in_place(&mut self) {
        match self {
            Stamp(IdTree::Flag(false), EventTree::Tuple(_, _, _)) => {
                return;
            }
            Stamp(IdTree::Flag(true), e @ EventTree::Tuple(_, _, _)) => {
                *e = EventTree::Value(e.max());
                return;
            }
            Stamp(_, EventTree::Value(_)) => {
                return;
            }
            Stamp(IdTree::Tuple(il, ir), EventTree::Tuple(_, el, er)) => {
                let il = &**il;
                let ir = &**ir;
                let el = Arc::make_mut(el);
                let er = Arc::make_mut(er);
                if let IdTree::Flag(true) = il {
                    let mut er2 = Stamp(ir.clone(), er.clone());
                    er2.fill_in_place();

                    let left = EventTree::Value(::std::cmp::max(el.max(), er2.1.min_normalized()));
                    *el = left;
                    *er = er2.1;
                } else if let IdTree::Flag(true) = ir {
                    let mut el2 = Stamp(il.clone(), el.clone());
                    el2.fill_in_place();

                    let right = EventTree::Value(::std::cmp::max(er.max(), el2.1.min_normalized()));
                    *el = el2.1;
                    *er = right;
                } else {
                    let mut el2 = Stamp(il.clone(), el.clone());
                    el2.fill_in_place();

                    let mut er2 = Stamp(ir.clone(), er.clone());
                    er2.fill_in_place();

                    *el = el2.1;
                    *er = er2.1;
                }
            }
        }
        self.normalize_in_place();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn id_tree_normalize_in_place() {
        let mut id_tree = IdTree::Tuple(
            Arc::new(IdTree::Flag(true)),
            Arc::new(IdTree::Tuple(
                Arc::new(IdTree::Flag(true)),
                Arc::new(IdTree::Flag(true)),
            )),
        );

        id_tree.normalize_in_place();

        assert_matches!(id_tree, IdTree::Flag(true));
    }

    #[test]
    fn event_tree_normalize_in_place_1() {
        let mut event_tree = EventTree::Tuple(
            2,
            Arc::new(EventTree::Value(1)),
            Arc::new(EventTree::Value(1)),
        );

        event_tree.normalize_in_place();

        assert_matches!(event_tree, EventTree::Value(3));
    }

    #[test]
    fn event_tree_normalize_in_place_2() {
        let mut event_tree = EventTree::Tuple(
            2,
            Arc::new(EventTree::Tuple(
                2,
                Arc::new(EventTree::Value(1)),
                Arc::new(EventTree::Value(0)),
            )),
            Arc::new(EventTree::Value(3)),
        );

        event_tree.normalize_in_place();

        assert_eq!(
            event_tree,
            EventTree::Tuple(
                4,
                Arc::new(EventTree::Tuple(
                    0,
                    Arc::new(EventTree::Value(1)),
                    Arc::new(EventTree::Value(0))
                )),
                Arc::new(EventTree::Value(1))
            )
        );
    }

    #[test]
    fn comparison_after_fork_and_no_events() {
        let stamp = Stamp::seed();

        let (left, right) = stamp.fork();

        assert!(stamp.less_than_or_equal(&left));
        assert!(stamp.less_than_or_equal(&right));

        assert!(left.less_than_or_equal(&stamp));
        assert!(right.less_than_or_equal(&stamp));

        let (left_left, left_right) = left.fork();

        assert!(stamp.less_than_or_equal(&left_left));
        assert!(stamp.less_than_or_equal(&left_right));
        assert!(left.less_than_or_equal(&left_left));
        assert!(left.less_than_or_equal(&left_right));

        assert!(left_left.less_than_or_equal(&stamp));
        assert!(left_right.less_than_or_equal(&stamp));
        assert!(left_left.less_than_or_equal(&left));
        assert!(left_right.less_than_or_equal(&left));

        assert!(right.less_than_or_equal(&left_left));
        assert!(right.less_than_or_equal(&left_right));
        assert!(left_left.less_than_or_equal(&right));
        assert!(left_right.less_than_or_equal(&right));
    }

    #[test]
    fn comparison_after_fork_and_events() {
        let stamp = Stamp::seed();

        let (left, right) = stamp.fork();
        let left = left.event();
        let right = right.event();

        assert!(stamp.less_than_or_equal(&left));
        assert!(stamp.less_than_or_equal(&right));

        assert!(!left.less_than_or_equal(&stamp));
        assert!(!right.less_than_or_equal(&stamp));

        let (left_left, left_right) = left.fork();
        let left_left = left_left.event();
        let left_right = left_right.event();

        assert!(stamp.less_than_or_equal(&left_left));
        assert!(stamp.less_than_or_equal(&left_right));
        assert!(left.less_than_or_equal(&left_left));
        assert!(left.less_than_or_equal(&left_right));

        assert!(!left_left.less_than_or_equal(&stamp));
        assert!(!left_right.less_than_or_equal(&stamp));
        assert!(!left_left.less_than_or_equal(&left));
        assert!(!left_right.less_than_or_equal(&left));

        assert!(!right.less_than_or_equal(&left_left));
        assert!(!right.less_than_or_equal(&left_right));
        assert!(!left_left.less_than_or_equal(&right));
        assert!(!left_right.less_than_or_equal(&right));
    }

    #[test]
    fn comparison_after_join() {
        let stamp = Stamp::seed();

        let (left, right) = stamp.fork();
        let left = left.event();
        let right = right.event();

        let joined = Stamp::join(&left, &right).unwrap();

        assert!(stamp.less_than_or_equal(&joined));
        assert!(left.less_than_or_equal(&joined));
        assert!(right.less_than_or_equal(&joined));
    }

    #[test]
    fn joining_independent_stamps_returns_error() {
        let stamp1 = Stamp::seed();
        let stamp2 = Stamp::seed();

        assert_eq!(
            Stamp::join(&stamp1, &stamp2),
            Err(JoinError::IndependentStamps)
        );
    }

    #[test]
    fn independent_stamps_comparison() {
        let stamp1 = Stamp::seed();
        let stamp2 = Stamp::seed();

        assert!(stamp1.less_than_or_equal(&stamp2));
        assert!(stamp2.less_than_or_equal(&stamp1));
    }
}
