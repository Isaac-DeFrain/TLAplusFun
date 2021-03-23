# AsyncPeerDiscovery

This is a formal specification of asynchronous peer discovery in Tezos

Nodes wishing to join the network must first communicate with a DNS to get an initial set of peers with whom they will go on to establish bidirectional encrypted communication channels. This spec only covers the initial peer retrieval from the DNS.

## AsyncPeerDiscovery_extra

This is the same spec as `AsyncPeerDiscovery` with the addition of nodes exchanging peers with one another.
