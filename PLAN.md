# Minimalloc Integration Plan

**1. Schedule Separation (`array.pl`)**
*   Modify `realize/1` and `create_schedule/2` to distinguish between intermediate arrays and explicitly requested output arrays.
*   Calculate execution lifetimes (`Start` and `End`) only for the intermediate arrays.
*   Exclude the output arrays from the `minimalloc` process entirely.

**2. Run Minimalloc on Intermediates (`array.pl`)**
*   Group the intermediate arrays by `device`.
*   Calculate the byte size for each intermediate array (`datasize * DTypeByteSize`) and pad it to a strict alignment boundary (e.g., 8 bytes).
*   Run `minimalloc:minimalloc/2` to compute `ByteOffset`s and the total required capacity for the intermediate arrays.
*   Convert the `ByteOffset`s to `ElementOffset`s (`ByteOffset // DTypeByteSize`).

**3. Allocation (`array.pl`)**
*   Allocate a single shared memory pool per device for the intermediate arrays, sized to the capacity found by `minimalloc`.
*   Allocate separate, dedicated data buffers for each output array (retaining the current behavior).

**4. Graph Rebuilding & State Mapping (`array.pl`)**
*   Iterate through the schedule to build a new execution graph of array dictionaries:
    *   **For Intermediate Arrays**: 
        *   Create a new array dict with an updated `view` that incorporates the `ElementOffset`.
        *   Assign a *fresh* uninstantiated variable to its `data` field.
        *   Bind this new `data` variable to the shared memory pool.
        *   *(This ensures the user's original references to the intermediate arrays retain their original view and unbound `data` variables).*
    *   **For Output Arrays**: 
        *   Create a new array dict where the `op` history points to the newly created intermediate array dicts.
        *   Keep the *original* `data` variable from the user's array dict.
        *   Bind this `data` variable to the newly allocated dedicated buffer.

**5. Execution (`array.pl`)**
*   Compile and run the kernels using the newly rebuilt schedule.
*   The kernels will inherently use the updated view offsets to safely read/write to the shared pool for intermediates, and write final results to the dedicated output buffers.
*   User-held intermediate arrays remain safe and unbound, while user-held output arrays get naturally populated.
