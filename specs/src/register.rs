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

// NOTE: LIMITATION
// - The MutLinearizer should be specified in the method
// - Type problem: the linearization queue is parametrized by the linearizer type
// - Polymorphism is hard
#[allow(dead_code)]
pub trait LinRegisterClient<C, ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    type ReadErr: RegisterError<RL, RegisterRead>;

    type WriteErr: RegisterError<ML, RegisterWrite>;

    type Timestamp;

    spec fn read_lin_requires(lin: RL) -> bool;

    spec fn write_lin_requires(lin: ML) -> bool;

    spec fn register_loc(self) -> Loc;

    spec fn inv(self) -> bool;

    fn read(&mut self, lin: Tracked<RL>) -> (r: Result<
        (Option<u64>, Self::Timestamp, Tracked<RL::Completion>),
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

    // TODO(writes): make writes behind a shared ref.
    // Problem: there is only a single tracked ClientCtrToken which cannot be shared between
    // threads
    fn write(&mut self, value: Option<u64>, lin: Tracked<ML>) -> (r: Result<
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

pub struct RegisterRead {
    /// resource location
    pub id: Ghost<Loc>,
}

pub struct RegisterWrite {
    /// resource location
    pub id: Ghost<Loc>,
    pub new_value: Option<u64>,
}

impl ReadOperation for RegisterRead {
    type Resource = GhostVarAuth<Option<u64>>;

    type ExecResult = Option<u64>;

    open spec fn requires(self, r: Self::Resource, e: Self::ExecResult) -> bool {
        &&& r.id() == self.id
        &&& r@ == e
    }
}

pub struct OwnedReadPerm {
    pub tracked register: GhostVar<Option<u64>>,
}

impl ReadLinearizer<RegisterRead> for OwnedReadPerm {
    type Completion = GhostVar<Option<u64>>;

    open spec fn namespaces(self) -> ISet<int> {
        ISet::empty()
    }

    open spec fn pre(self, op: RegisterRead) -> bool {
        &&& op.id == self.register.id()
    }

    open spec fn post(
        self,
        op: RegisterRead,
        exec_res: Option<u64>,
        completion: Self::Completion,
    ) -> bool {
        &&& op.id == self.register.id()
        &&& op.id == completion.id()
        &&& self.register == completion
        &&& exec_res == completion@
    }

    proof fn apply(
        tracked self,
        op: RegisterRead,
        tracked resource: &GhostVarAuth<Option<u64>>,
        exec_res: &Option<u64>,
    ) -> (tracked result: Self::Completion) {
        resource.agree(&self.register);
        self.register
    }

    proof fn peek(tracked &self, op: RegisterRead, tracked resource: &GhostVarAuth<Option<u64>>) {
    }
}

impl MutOperation for RegisterWrite {
    type Resource = GhostVarAuth<Option<u64>>;

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

pub struct OwnedWritePerm {
    pub value: Option<u64>,
    pub tracked register: GhostVar<Option<u64>>,
}

impl MutLinearizer<RegisterWrite> for OwnedWritePerm {
    type Completion = GhostVar<Option<u64>>;

    open spec fn namespaces(self) -> ISet<int> {
        ISet::empty()
    }

    open spec fn pre(self, op: RegisterWrite) -> bool {
        op.id == self.register.id()
    }

    open spec fn post(self, op: RegisterWrite, exec_res: (), completion: Self::Completion) -> bool {
        &&& op.id == self.register.id()
        &&& op.id == completion.id()
        &&& op.new_value == completion@
    }

    proof fn apply(
        tracked self,
        op: RegisterWrite,
        tracked resource: &mut GhostVarAuth<Option<u64>>,
        new_state: (),
        exec_res: &(),
    ) -> (tracked result: Self::Completion) {
        let tracked OwnedWritePerm { value, mut register } = self;

        resource.update(&mut register, op.new_value);
        register
    }

    proof fn peek(tracked &self, op: RegisterWrite, tracked resource: &GhostVarAuth<Option<u64>>) {
    }
}

} // verus!
