# Server Proof

The server's proof is remarkably easy.
The server only holds onto a timestamp, value pair (`MonotonicRegisterInner` in `register.rs`,
guarded by an `RwLock<_, MonotonicRegisterInv>`).
When receiving a read request (`Get`/`GetTimestamp`), it returns the current value/timestamp.
When receiving a write request, it updates its value if the timestamp is greater.

Every request (`GetRequest`, `GetTimestampRequest`, `WriteRequest` in `proto/`) carries, alongside
its plain data, a ghost lower-bound resource for the server it is addressed to (a
`MonotonicTimestampResource` in `LowerBound` state, reached through the request's
`ServerUniverseLb`/`servers()` map). This is not a wire field: on the wire only `value`/`timestamp`
are (de)serialized (see the `serde_impls` in `proto/get.rs`/`proto/write.rs`); the lower-bound and
commitment resources are ghost/tracked state threaded alongside the message and reconstructed on
the deserializing side (`axiom_forge`, guarded by `assume(false)`, since a real network cannot ship
ghost state — the client and server processes each hold/attach their own tracked copies).

The server extracts this lower bound via `{Get,GetTimestamp,Write}Request::server_lower_bound`/
`destruct`, and certifies it against its own current resource with
`MonotonicTimestampResource::lemma_lower_bound`, called in `MonotonicRegisterInner::read`,
`read_timestamp`, and at the end of `write` (`register.rs`). This lemma is exactly the mechanism
that ensures the request's lower bound is in fact no greater than the server's current resource,
i.e. that clients never observe a server "going back in time" on the timestamp they last observed
from it. This is enforced by the resource algebra (`MonotonicTimestampResource`'s `HalfRightToAdvance`/
`LowerBound` states), not by an explicit runtime check on plain data.

The other resource the server keeps is the commitment from the writer whose value it is holding
(`WriteCommitment = GhostPersistentPointsTo<Timestamp, Option<u64>>`, held in
`MonotonicRegisterInner::commitment`). `WriteRequest` carries the writer's commitment for the
timestamp/value being written (`commitment: Tracked<WriteCommitment>`, with its type invariant
requiring `commitment.key() == timestamp` and `commitment.value() == value`); on a successful write
the server adopts this commitment as its own (see the `write` branch in
`MonotonicRegisterInner::write`, which replaces `self.commitment` with the one destructed from the
request). Because `WriteCommitment` is a `GhostPersistentPointsTo` over the commitment map defined
in `invariants/committed_to.rs` (`Commitments::commitment_auth`, allocated once per timestamp via
`Commitments::alloc_value`/`alloc`), two commitments for the same timestamp are guaranteed (by
`agree`/`GhostMapAuth` uniqueness) to carry the same value. This is what lets a client that observes
a single commitment for a given timestamp conclude there is no other value committed at that
timestamp, ruling out writer equivocation.

`Get`/`GetTimestamp` responses (`GetResponse`, in `proto/get.rs`) piggy-back a duplicate of the
server's currently-held commitment (`GetResponse::commitment`), so a reader can also learn the
committed value/uniqueness for the timestamp it read, not just writers.

## TODOs

None outstanding for lowerbound-checking or commitment-holding — both are implemented as described
above. Remaining gaps, if any, belong to the client-side proof (see `client/Proof.md`'s own TODO
list) rather than the server.
