import Vsa.Sim.ExitRuntimeData

open Vsa.MemRepr

namespace Vsa.Sim

private theorem readLE_exitRegion_agree
    {regions : List (Nat × Nat)} {m m' : Mem}
    (hag : AgreeP (ExitRegionFoot regions) m m')
    (address width : Nat) (hregion : (address, width) ∈ regions) :
    readLE m address width = readLE m' address width :=
  readLE_agreeP hag width address (fun k hk =>
    ⟨(address, width), hregion,
      Nat.le_add_right address k, Nat.add_lt_add_left hk address⟩)

theorem ExitIdleFile.transport {m m' : Mem} {file flags descriptor : Nat}
    (h : ExitIdleFile m file flags descriptor)
    (hag : AgreeP (ExitRegionFoot (exitIdleFileRegions file)) m m') :
    ExitIdleFile m' file flags descriptor := by
  have hr := readLE_exitRegion_agree hag
  exact {
    flags_read := (hr (file + 16) 2 (by simp [exitIdleFileRegions])).symm.trans
      h.flags_read
    descriptor_read := (hr (file + 18) 2 (by simp [exitIdleFileRegions])).symm.trans
      h.descriptor_read
    readCount := (hr (file + 8) 4 (by simp [exitIdleFileRegions])).symm.trans
      h.readCount
    savedReadCount := (hr (file + 112) 4 (by simp [exitIdleFileRegions])).symm.trans
      h.savedReadCount
    cookie := (hr (file + 48) 8 (by simp [exitIdleFileRegions])).symm.trans
      h.cookie
    closeCallback := (hr (file + 80) 8 (by simp [exitIdleFileRegions])).symm.trans
      h.closeCallback
    ungetcBuffer := (hr (file + 88) 8 (by simp [exitIdleFileRegions])).symm.trans
      h.ungetcBuffer
    lineBuffer := (hr (file + 120) 8 (by simp [exitIdleFileRegions])).symm.trans
      h.lineBuffer
    lock := (hr (file + 160) 8 (by simp [exitIdleFileRegions])).symm.trans
      h.lock
    lockMode := (hr (file + 176) 4 (by simp [exitIdleFileRegions])).symm.trans
      h.lockMode }

theorem ExitRuntimeData.transport {m m' : Mem}
    (h : ExitRuntimeData m) (hag : AgreeP ExitRuntimeExtraFoot m m') :
    ExitRuntimeData m' := by
  have hr := readLE_exitRegion_agree hag
  have hidle (file : Nat)
      (hsub : ∀ region ∈ exitIdleFileRegions file,
        region ∈ exitRuntimeExtraRegions) :
      AgreeP (ExitRegionFoot (exitIdleFileRegions file)) m m' := by
    intro address ha
    obtain ⟨region, hregion, hlo, hhi⟩ := ha
    exact hag address ⟨region, hsub region hregion, hlo, hhi⟩
  obtain ⟨word, hword⟩ := h.atexitLock
  exact {
    atexit := (hr exitAtexitAddr 8 (by simp [exitRuntimeExtraRegions])).symm.trans
      h.atexit
    atexitLock := ⟨word,
      (hr exitAtexitLockAddr 8 (by simp [exitRuntimeExtraRegions])).symm.trans hword⟩
    stdioHandler :=
      (hr exitStdioHandlerAddr 8 (by simp [exitRuntimeExtraRegions])).symm.trans
        h.stdioHandler
    glueNext := (hr exitGlueAddr 8 (by simp [exitRuntimeExtraRegions])).symm.trans
      h.glueNext
    glueCount := (hr (exitGlueAddr + 8) 4 (by simp [exitRuntimeExtraRegions])).symm.trans
      h.glueCount
    glueFiles := (hr (exitGlueAddr + 16) 8 (by simp [exitRuntimeExtraRegions])).symm.trans
      h.glueFiles
    stdin := h.stdin.transport (hidle exitStdin (by
      intro region hregion
      simp [exitRuntimeExtraRegions, hregion]))
    stderr := h.stderr.transport (hidle exitStderr (by
      intro region hregion
      simp [exitRuntimeExtraRegions, hregion]))
    stdoutClose :=
      (hr (consoleStdout + 80) 8 (by simp [exitRuntimeExtraRegions])).symm.trans
        h.stdoutClose
    stdoutUngetc :=
      (hr (consoleStdout + 88) 8 (by simp [exitRuntimeExtraRegions])).symm.trans
        h.stdoutUngetc
    stdoutLine :=
      (hr (consoleStdout + 120) 8 (by simp [exitRuntimeExtraRegions])).symm.trans
        h.stdoutLine }

end Vsa.Sim
