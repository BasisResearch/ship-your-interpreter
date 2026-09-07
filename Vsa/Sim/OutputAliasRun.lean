import Vsa.Sim.OutputAliasRun.Groups

/-! Complete dense-state execution of the admitted output-alias program. -/

open Vsa.Machine Vsa.Refine Vsa.While
namespace Vsa.Sim.OutputAliasLoaded

theorem snapshot_halts_twoLF : Halts snapshotConfig "\n\n" 0 := by
  obtain ⟨c000, path000, h000⟩ := traceStart
  obtain ⟨c001, s001, h001⟩ := runGroup001 h000
  have path001 : Steps snapshotConfig c001 := path000.trans s001
  obtain ⟨c002, s002, h002⟩ := runGroup002 h001
  have path002 : Steps snapshotConfig c002 := path001.trans s002
  obtain ⟨c003, s003, h003⟩ := runGroup003 h002
  have path003 : Steps snapshotConfig c003 := path002.trans s003
  obtain ⟨c004, s004, h004⟩ := runGroup004 h003
  have path004 : Steps snapshotConfig c004 := path003.trans s004
  obtain ⟨c005, s005, h005⟩ := runGroup005 h004
  have path005 : Steps snapshotConfig c005 := path004.trans s005
  obtain ⟨c006, s006, h006⟩ := runGroup006 h005
  have path006 : Steps snapshotConfig c006 := path005.trans s006
  obtain ⟨c007, s007, h007⟩ := runGroup007 h006
  have path007 : Steps snapshotConfig c007 := path006.trans s007
  obtain ⟨c008, s008, h008⟩ := runGroup008 h007
  have path008 : Steps snapshotConfig c008 := path007.trans s008
  obtain ⟨c009, s009, h009⟩ := runGroup009 h008
  have path009 : Steps snapshotConfig c009 := path008.trans s009
  obtain ⟨c010, s010, h010⟩ := runGroup010 h009
  have path010 : Steps snapshotConfig c010 := path009.trans s010
  obtain ⟨c011, s011, h011⟩ := runGroup011 h010
  have path011 : Steps snapshotConfig c011 := path010.trans s011
  obtain ⟨c012, s012, h012⟩ := runGroup012 h011
  have path012 : Steps snapshotConfig c012 := path011.trans s012
  obtain ⟨c013, s013, h013⟩ := runGroup013 h012
  have path013 : Steps snapshotConfig c013 := path012.trans s013
  obtain ⟨c014, s014, h014⟩ := runGroup014 h013
  have path014 : Steps snapshotConfig c014 := path013.trans s014
  obtain ⟨c015, s015, h015⟩ := runGroup015 h014
  have path015 : Steps snapshotConfig c015 := path014.trans s015
  obtain ⟨c016, s016, h016⟩ := runGroup016 h015
  have path016 : Steps snapshotConfig c016 := path015.trans s016
  obtain ⟨c017, s017, h017⟩ := runGroup017 h016
  have path017 : Steps snapshotConfig c017 := path016.trans s017
  obtain ⟨c018, s018, h018⟩ := runGroup018 h017
  have path018 : Steps snapshotConfig c018 := path017.trans s018
  obtain ⟨c019, s019, h019⟩ := runGroup019 h018
  have path019 : Steps snapshotConfig c019 := path018.trans s019
  obtain ⟨σf, hh, ho⟩ := run285 h019
  refine ⟨c019, σf, path019, hh, ?_⟩
  change String.join σf.sailOutput.toList = "\n\n"
  rw [ho]
  rfl

#print axioms snapshot_halts_twoLF

end Vsa.Sim.OutputAliasLoaded
