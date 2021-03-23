# PeerDiscovery

This is a formal specification for synchronous peer discovery in Tezos. As in many P2P metworks, nodes wishing to join the network must first communicate with a DNS to get a set of peers, with whom further communication will tkae place.

In this spec, joining nodes must first contact the DNS. The DNS will immediately respond with a set of two or more node IDs (not including the node that requested the peers). Once a node obtains peers, they can than request peers from any of these nodes.
