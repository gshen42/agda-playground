open import Data.Nat using (ℕ)

module CBCAST.Protocol where

record Protocol : Set₁ where
  field
    MessageMetadata  : Set

    ProcessMetadata  : Set

    processMetadata₀ : (pid : ℕ) → ProcessMetadata

    BroadcastHandler : (pid : ℕ)
                     → (msgMeta     : MessageMetadata)
                     → (procMeta    : ProcessMetadata)
                     → (procMetaNew : ProcessMetadata)
                     → Set

    Deliverable      : (pid : ℕ)
                     → (msgMeta  : MessageMetadata)
                     → (procMeta : ProcessMetadata)
                     → Set

    DeliverHandler   : (pid : ℕ)
                     → (msgMeta     : MessageMetadata)
                     → (procMeta    : ProcessMetadata)
                     → (procMetaNew : ProcessMetadata)
                     → Set
