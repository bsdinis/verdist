use vstd::logatom::MutLinearizer;
use vstd::logatom::MutOperation;
use vstd::logatom::ReadLinearizer;
use vstd::logatom::ReadOperation;
use vstd::prelude::*;
use vstd::resource::ghost_var::GhostVar;
use vstd::resource::ghost_var::GhostVarAuth;
use vstd::resource::Loc;

verus! {

pub trait RegisterError<L, Op> {
    spec fn err_ensures(self, op: Op, lin: L) -> bool;
}

pub type ReadReturn<const N: usize, Timestamp, Completion> = (
    Option<[u8; N]>,
    Timestamp,
    Tracked<Completion>,
);

// NOTE: LIMITATION
// - The MutLinearizer should be specified in the method
// - Type problem: the linearization queue is parametrized by the linearizer type
// - Polymorphism is hard
#[allow(dead_code)]
pub trait LinRegisterClient<const N: usize, C, ML, RL> where
    ML: MutLinearizer<RegisterWrite<N>>,
    RL: ReadLinearizer<RegisterRead<N>>,
 {
    type ReadErr: RegisterError<RL, RegisterRead<N>>;

    type WriteErr: RegisterError<ML, RegisterWrite<N>>;

    type Timestamp;

    spec fn read_lin_requires(lin: RL) -> bool;

    spec fn write_lin_requires(lin: ML) -> bool;

    spec fn register_loc(self) -> Loc;

    spec fn inv(self) -> bool;

    fn read(&mut self, lin: Tracked<RL>) -> (r: Result<
        ReadReturn<N, Self::Timestamp, RL::Completion>,
        Self::ReadErr,
    >)
        requires
            lin@.pre(RegisterRead { id: Ghost(old(self).register_loc()) }),
            Self::read_lin_requires(lin@),
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).register_loc() == old(self).register_loc(),
            r is Ok ==> ({
                let (val, ts, compl) = r->Ok_0;
                lin@.post(RegisterRead { id: Ghost(final(self).register_loc()) }, val, compl@)
            }),
            r is Err ==> ({
                let err = r->Err_0;
                let op = RegisterRead { id: Ghost(final(self).register_loc()) };
                err.err_ensures(op, lin@)
            }),
    ;

    // NOTE(writes): it would be nice for `write` to take `&self` (a shared ref), matching
    // `read`, so that writes from multiple threads/tasks could be in flight concurrently the
    // same way reads can. This is intentionally left as `&mut self` rather than "fixed": the
    // client-side implementation (e.g. `abd`'s `AbdPool`) holds a single, non-`Copy` tracked
    // `ClientCtrToken` permission that `write` mutably borrows (see
    // `state.commitments.alloc_value(self.client_ctr_token.borrow_mut(), ...)` in
    // `abd/src/client/mod.rs`) to allocate a fresh commitment slot per write. A tracked
    // resource can only ever be borrowed mutably by one caller at a time, so moving to `&self`
    // here would require redesigning that allocation to go through something like an internal
    // lock/atomic-invariant-guarded token instead of a plain field -- a real restructuring of
    // the write path's proof, not a signature tweak, so it is left as a documented limitation
    // rather than forced through here.
    fn write(&mut self, value: Option<[u8; N]>, lin: Tracked<ML>) -> (r: Result<
        Tracked<ML::Completion>,
        Self::WriteErr,
    >)
        requires
            old(self).inv(),
            lin@.pre(RegisterWrite { id: Ghost(old(self).register_loc()), new_value: value }),
            Self::write_lin_requires(lin@),
        ensures
            final(self).inv(),
            final(self).register_loc() == old(self).register_loc(),
            r is Ok ==> ({
                let comp = r->Ok_0;
                &&& lin@.post(
                    RegisterWrite { id: Ghost(final(self).register_loc()), new_value: value },
                    (),
                    comp@,
                )
            }),
            r is Err ==> ({
                let err = r->Err_0;
                let op = RegisterWrite { id: Ghost(final(self).register_loc()), new_value: value };
                err.err_ensures(op, lin@)
            }),
    ;
}

pub struct RegisterRead<const N: usize> {
    /// resource location
    pub id: Ghost<Loc>,
}

pub struct RegisterWrite<const N: usize> {
    /// resource location
    pub id: Ghost<Loc>,
    pub new_value: Option<[u8; N]>,
}

impl<const N: usize> ReadOperation for RegisterRead<N> {
    type Resource = GhostVarAuth<Option<[u8; N]>>;

    type ExecResult = Option<[u8; N]>;

    open spec fn requires(self, r: Self::Resource, e: Self::ExecResult) -> bool {
        &&& r.id() == self.id
        &&& r@ == e
    }
}

pub struct OwnedReadPerm<const N: usize> {
    pub tracked register: GhostVar<Option<[u8; N]>>,
}

impl<const N: usize> ReadLinearizer<RegisterRead<N>> for OwnedReadPerm<N> {
    type Completion = GhostVar<Option<[u8; N]>>;

    open spec fn namespaces(self) -> ISet<int> {
        ISet::empty()
    }

    open spec fn pre(self, op: RegisterRead<N>) -> bool {
        &&& op.id == self.register.id()
    }

    open spec fn post(
        self,
        op: RegisterRead<N>,
        exec_res: Option<[u8; N]>,
        completion: Self::Completion,
    ) -> bool {
        &&& op.id == self.register.id()
        &&& op.id == completion.id()
        &&& self.register == completion
        &&& exec_res == completion@
    }

    proof fn apply(
        tracked self,
        op: RegisterRead<N>,
        tracked resource: &GhostVarAuth<Option<[u8; N]>>,
        exec_res: &Option<[u8; N]>,
    ) -> (tracked result: Self::Completion) {
        resource.agree(&self.register);
        self.register
    }

    proof fn peek(
        tracked &self,
        op: RegisterRead<N>,
        tracked resource: &GhostVarAuth<Option<[u8; N]>>,
    ) {
    }
}

impl<const N: usize> MutOperation for RegisterWrite<N> {
    type Resource = GhostVarAuth<Option<[u8; N]>>;

    type ExecResult = ();

    type NewState = ();

    open spec fn requires(
        self,
        pre: Self::Resource,
        new_state: Self::NewState,
        e: Self::ExecResult,
    ) -> bool {
        &&& pre.id() == self.id
    }

    open spec fn ensures(
        self,
        pre: Self::Resource,
        post: Self::Resource,
        new_state: Self::NewState,
    ) -> bool {
        &&& pre.id() == post.id()
        &&& post@ == self.new_value
    }
}

pub struct OwnedWritePerm<const N: usize> {
    pub value: Option<[u8; N]>,
    pub tracked register: GhostVar<Option<[u8; N]>>,
}

impl<const N: usize> MutLinearizer<RegisterWrite<N>> for OwnedWritePerm<N> {
    type Completion = GhostVar<Option<[u8; N]>>;

    open spec fn namespaces(self) -> ISet<int> {
        ISet::empty()
    }

    open spec fn pre(self, op: RegisterWrite<N>) -> bool {
        op.id == self.register.id()
    }

    open spec fn post(
        self,
        op: RegisterWrite<N>,
        exec_res: (),
        completion: Self::Completion,
    ) -> bool {
        &&& op.id == self.register.id()
        &&& op.id == completion.id()
        &&& op.new_value == completion@
    }

    proof fn apply(
        tracked self,
        op: RegisterWrite<N>,
        tracked resource: &mut GhostVarAuth<Option<[u8; N]>>,
        new_state: (),
        exec_res: &(),
    ) -> (tracked result: Self::Completion) {
        let tracked OwnedWritePerm { value, mut register } = self;

        resource.update(&mut register, op.new_value);
        register
    }

    proof fn peek(
        tracked &self,
        op: RegisterWrite<N>,
        tracked resource: &GhostVarAuth<Option<[u8; N]>>,
    ) {
    }
}

} // verus!
