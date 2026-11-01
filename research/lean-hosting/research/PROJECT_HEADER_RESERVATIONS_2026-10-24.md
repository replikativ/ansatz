# Project discovery header output reservations

The [focused regression](../measurements/project-header-reservations.json)
reproduces a concrete configuration defect in the first coupled P1/P2 capture:
16 KiB aggregate header-output capacity and a 16 KiB per-header bound allow only
one source header. The second header is refused before dispatch. A separate
discovery with 64 KiB aggregate capacity processes both independent roots in
order. No runtime implementation or general budget default changes here.

## Reservation contract

[`project-discovery/call-header!`](../src/prototype/project_discovery.clj)
reserves the entire configured `:header-limits :max-output-bytes` before each
source header call. It adds that bound to cumulative `:header-output-reserved`;
the reservation is not reduced to the returned JSON's actual byte length.
Scheduling duplicate imports once does not eliminate the second independent
source's header call.

| Configuration | Per-header bound | Aggregate capacity | Two independent headers |
| --- | ---: | ---: | --- |
| Failed capture boundary | 16,384 bytes | 16,384 bytes | Second call refused |
| Separate corrected fixture | 16,384 bytes | 65,536 bytes | Two calls; 32,768 bytes reserved |

The campaign declares at most four source modules. Its next explicitly reviewed
capture should provision `4 × 16,384 = 65,536` aggregate bytes and check this
experiment-specific relationship before its expensive base construction/restore.
This is a host-output capacity change, not guest fuel or permission expansion.
General library callers may deliberately set tighter aggregate caps; imposing
the product globally would change that valid refusal policy.

## What the small fixture establishes

One reference-backend test uses real filesystem capture, the unchanged discovery
implementation, modeled header transport and actual resident adoption. With the
exact failing capacity it observes:

- A's header dispatches once; D is captured but its header never dispatches.
- The exact error is `Project discovery cannot reserve next header output`.
- The last completed header packet and canonical checkpoint World/session
  remain intact, with zero outstanding helper-fuel reservation.
- The separately retained input Context remains unchanged.

A new discovery from the original packet, with 64 KiB capacity, dispatches two
headers and returns roots/order A,D. Its returned packet successfully adopts.
This is a separate attempt, not resumption of the failed packet.

Validation passed **1 test / 20 assertions**, zero failures/errors, in
**3.365 seconds**, under a 384 MiB heap. Peak group RSS was **493,277,184 bytes**.
All **370** input hashes matched afterward and the process group was disposed.
The run reused 48 unchanged prebuilt Java classes; it performed no fresh Java
compilation, full Init restore, actual Lean frontend or native compiler work.
The new test is in the existing registered discovery test namespace.

## Relationship to the actual coupled failure

The earlier full coupled run completed fresh Init checking, single-A loading and
two calls, then matched the issued native selection of 631 modules. It failed
during P2 preparation before advance/reset. The original message/stack was not
retained across process exit. This regression proves a deterministic blocker in
that capture, but cannot certify the lost exception's exact first cause.

The separately accepted [public single-file P1](PROJECT_LOADING.md)
remains valid. Corrected discovery capacity alone establishes neither actual
native reset nor full P2 acceptance. Before another full run, preserve bounded
cause message/stack and phase diagnostics without printing Throwable/ex-data or
Worlds, and independently review the new capture's complete inputs and limits.
