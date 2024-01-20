# Formal model of Kafka in Alloy 6
Apache Kafka is a distributed, fault-tolerant and highly available open-source technology that utilizes the publish-subscribe communication model to stream large volumes of data. It is widely being used in various domains in the industry such as finance, entertainment, online education, and e-commerce, for real-time data processing and analytics. The purpose of this project is to model the internal architecture of Kafka using Alloy 6 to demonstrate how the behavior of a complex distributed system can be formally specified in Alloy 6, and its key properties of fault-tolerance, data availability and consistency, and service availability can be verified. This project also provides insight into how Kafka maintains the properties that it claims to have, and the circumstances under which these properties may get weakened.

# Files
```
.
├── README.md               // this file
├── kafka_main.als          // the main model file defining and checking behaviour of the model
├── signatures.als          // defines signatures
├── invariants.als          // defines invariants
├── basic_assertions.als    // defines assertions for checking model validity
├── actions.als             // defines transitions
├── verify_actions.als      // contains run and assertion commands to verify transitions in isolation
└── functions.als           // contains helper functions
```