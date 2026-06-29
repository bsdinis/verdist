# Verdist

`verdist` is a library for building distributed systems and verifying them.

At a high-level, `verdist` gives 3 elements:
- Network abstractions: a `Channel` trait to have generic implementations that can be plug and play;
- Pool abstractions: allows for handling multiple connections. In particular you can `broadcast` to a pool of servers and `wait_for` a particular condition;
- RPC abstractions: rpc channels, pool message agregators and request contexts

More docs incoming
