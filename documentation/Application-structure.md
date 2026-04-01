# Waterproof's application structure

Waterproof is built on the proof assistant *CoQ*.
It communicates with the proof assistant using a library called *SerAPI*.
This communication is indirect: Waterproof starts an application called *wpwrapper*, 
which in turn runs several instances of *sertop*.

The connection between Waterproof and the wrapper is maintained by the *TCPManager*.
It manages an array of *workers*, found in *SerapiWorkerTCP*.
Every worker communicates with its own instance of *sertop*. 
It handles the communication for one notebook.

When starting a new notebook within Waterproof, the method *startCoq* in *CoqInteraction.vue*
asks the *TCPManager* to create a new worker.

## Adding functionality to the worker

After creating the worker, the method *startCoq* adorns it with a *CoqSerapiProcessors* object,
which attaches a *tagger* and several *CoqSerapiProcessors* to the worker.

The *tagger* is necessary to link any response of SerAPI back to the original message.

The processors provide the functionality to send the correct messages to SerAPI, for instance when 
a new sentence should be executed, and handles the response by SerAPI.
Because the communication with SerAPI is asynchronous, a large part of the tasks of the Processors is 
to manage this asynchronicity, for instance with the use of locks.

The responsibility for composing the correct message, the correct string, is deferred to 
the *SerapiCommandFactory*.

## SerapiProcessors

Currently, the following CoqSerapiProcessors are implemented:
* SerapiContentProcessor
* SerapiExecutionProcessor
* SerapiSearchProcessor

### SerapiContentProcessor

The SerapiContentProcessor manages *adding* and *canceling* sentences to the document.
After sentences are added, they are parsed by SerAPI, but they are not yet executed.

### SerapiExecutionProcessor

The SerapiExecutionProcessor manages *execution* of sentences.
A typical example is applying a tactic in a proof of a lemma.
The execution of such a sentence usually changes the current *goal*, i.e. what is left to prove.
The SerapiExecutionProcessor also handles such goal changes.

### SerapiSearchProcessor

The SerapiSearchProcessor manages *searches and other queries*.
After performing a search, SerAPI sends back a feedback message with search results.
This feedback message is processed by the SerapiSearchProcessor.

## SerapiState

On the side of Waterproof, we need to keep track of some aspects of the *state* of SerAPI and CoQ kernels. 
The aspects we keep track include which sentences are added to the SerAPI kernel,
and what was the corresponding id that SerAPI assigned to them.
We compute the aspects of the state purely based on what we send to SerAPI and the 
responses we get on the basis of them.
