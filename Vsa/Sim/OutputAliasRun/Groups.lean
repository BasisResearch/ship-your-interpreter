import Vsa.Sim.OutputAliasRun.Part00
import Vsa.Sim.OutputAliasRun.Part01
import Vsa.Sim.OutputAliasRun.Part02
import Vsa.Sim.OutputAliasRun.Part03
import Vsa.Sim.OutputAliasRun.Part04
import Vsa.Sim.OutputAliasRun.Part05
import Vsa.Sim.OutputAliasRun.Part06
import Vsa.Sim.OutputAliasRun.Part07
import Vsa.Sim.OutputAliasRun.Part08
import Vsa.Sim.OutputAliasRun.Part09
import Vsa.Sim.OutputAliasRun.Part10
import Vsa.Sim.OutputAliasRun.Part11
import Vsa.Sim.OutputAliasRun.Part12
import Vsa.Sim.OutputAliasRun.Part13
import Vsa.Sim.OutputAliasRun.Part14
-- discipline: allow(R7-conj-tower-def) Generated independent transition endpoints; each post is the named TraceHolds structure. Existentials bind reached configurations for Steps composition, not anonymous representation towers.

open Vsa.Machine Vsa.Refine Vsa.While
namespace Vsa.Sim.OutputAliasLoaded

theorem runGroup001 {c : Config}
    (h : TraceHolds traceD001 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD016 c' := by
  obtain ⟨c001, s001, h001⟩ := run001 h
  have path001 : Steps c c001 := s001
  obtain ⟨c002, s002, h002⟩ := run002 h001
  have path002 : Steps c c002 := path001.trans s002
  obtain ⟨c003, s003, h003⟩ := run003 h002
  have path003 : Steps c c003 := path002.trans s003
  obtain ⟨c004, s004, h004⟩ := run004 h003
  have path004 : Steps c c004 := path003.trans s004
  obtain ⟨c005, s005, h005⟩ := run005 h004
  have path005 : Steps c c005 := path004.trans s005
  obtain ⟨c006, s006, h006⟩ := run006 h005
  have path006 : Steps c c006 := path005.trans s006
  obtain ⟨c007, s007, h007⟩ := run007 h006
  have path007 : Steps c c007 := path006.trans s007
  obtain ⟨c008, s008, h008⟩ := run008 h007
  have path008 : Steps c c008 := path007.trans s008
  obtain ⟨c009, s009, h009⟩ := run009 h008
  have path009 : Steps c c009 := path008.trans s009
  obtain ⟨c010, s010, h010⟩ := run010 h009
  have path010 : Steps c c010 := path009.trans s010
  obtain ⟨c011, s011, h011⟩ := run011 h010
  have path011 : Steps c c011 := path010.trans s011
  obtain ⟨c012, s012, h012⟩ := run012 h011
  have path012 : Steps c c012 := path011.trans s012
  obtain ⟨c013, s013, h013⟩ := run013 h012
  have path013 : Steps c c013 := path012.trans s013
  obtain ⟨c014, s014, h014⟩ := run014 h013
  have path014 : Steps c c014 := path013.trans s014
  obtain ⟨c015, s015, h015⟩ := run015 h014
  have path015 : Steps c c015 := path014.trans s015
  exact ⟨c015, path015, h015⟩

#print axioms runGroup001

theorem runGroup002 {c : Config}
    (h : TraceHolds traceD016 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD031 c' := by
  obtain ⟨c016, s016, h016⟩ := run016 h
  have path016 : Steps c c016 := s016
  obtain ⟨c017, s017, h017⟩ := run017 h016
  have path017 : Steps c c017 := path016.trans s017
  obtain ⟨c018, s018, h018⟩ := run018 h017
  have path018 : Steps c c018 := path017.trans s018
  obtain ⟨c019, s019, h019⟩ := run019 h018
  have path019 : Steps c c019 := path018.trans s019
  obtain ⟨c020, s020, h020⟩ := run020 h019
  have path020 : Steps c c020 := path019.trans s020
  obtain ⟨c021, s021, h021⟩ := run021 h020
  have path021 : Steps c c021 := path020.trans s021
  obtain ⟨c022, s022, h022⟩ := run022 h021
  have path022 : Steps c c022 := path021.trans s022
  obtain ⟨c023, s023, h023⟩ := run023 h022
  have path023 : Steps c c023 := path022.trans s023
  obtain ⟨c024, s024, h024⟩ := run024 h023
  have path024 : Steps c c024 := path023.trans s024
  obtain ⟨c025, s025, h025⟩ := run025 h024
  have path025 : Steps c c025 := path024.trans s025
  obtain ⟨c026, s026, h026⟩ := run026 h025
  have path026 : Steps c c026 := path025.trans s026
  obtain ⟨c027, s027, h027⟩ := run027 h026
  have path027 : Steps c c027 := path026.trans s027
  obtain ⟨c028, s028, h028⟩ := run028 h027
  have path028 : Steps c c028 := path027.trans s028
  obtain ⟨c029, s029, h029⟩ := run029 h028
  have path029 : Steps c c029 := path028.trans s029
  obtain ⟨c030, s030, h030⟩ := run030 h029
  have path030 : Steps c c030 := path029.trans s030
  exact ⟨c030, path030, h030⟩

#print axioms runGroup002

theorem runGroup003 {c : Config}
    (h : TraceHolds traceD031 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD046 c' := by
  obtain ⟨c031, s031, h031⟩ := run031 h
  have path031 : Steps c c031 := s031
  obtain ⟨c032, s032, h032⟩ := run032 h031
  have path032 : Steps c c032 := path031.trans s032
  obtain ⟨c033, s033, h033⟩ := run033 h032
  have path033 : Steps c c033 := path032.trans s033
  obtain ⟨c034, s034, h034⟩ := run034 h033
  have path034 : Steps c c034 := path033.trans s034
  obtain ⟨c035, s035, h035⟩ := run035 h034
  have path035 : Steps c c035 := path034.trans s035
  obtain ⟨c036, s036, h036⟩ := run036 h035
  have path036 : Steps c c036 := path035.trans s036
  obtain ⟨c037, s037, h037⟩ := run037 h036
  have path037 : Steps c c037 := path036.trans s037
  obtain ⟨c038, s038, h038⟩ := run038 h037
  have path038 : Steps c c038 := path037.trans s038
  obtain ⟨c039, s039, h039⟩ := run039 h038
  have path039 : Steps c c039 := path038.trans s039
  obtain ⟨c040, s040, h040⟩ := run040 h039
  have path040 : Steps c c040 := path039.trans s040
  obtain ⟨c041, s041, h041⟩ := run041 h040
  have path041 : Steps c c041 := path040.trans s041
  obtain ⟨c042, s042, h042⟩ := run042 h041
  have path042 : Steps c c042 := path041.trans s042
  obtain ⟨c043, s043, h043⟩ := run043 h042
  have path043 : Steps c c043 := path042.trans s043
  obtain ⟨c044, s044, h044⟩ := run044 h043
  have path044 : Steps c c044 := path043.trans s044
  obtain ⟨c045, s045, h045⟩ := run045 h044
  have path045 : Steps c c045 := path044.trans s045
  exact ⟨c045, path045, h045⟩

#print axioms runGroup003

theorem runGroup004 {c : Config}
    (h : TraceHolds traceD046 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD061 c' := by
  obtain ⟨c046, s046, h046⟩ := run046 h
  have path046 : Steps c c046 := s046
  obtain ⟨c047, s047, h047⟩ := run047 h046
  have path047 : Steps c c047 := path046.trans s047
  obtain ⟨c048, s048, h048⟩ := run048 h047
  have path048 : Steps c c048 := path047.trans s048
  obtain ⟨c049, s049, h049⟩ := run049 h048
  have path049 : Steps c c049 := path048.trans s049
  obtain ⟨c050, s050, h050⟩ := run050 h049
  have path050 : Steps c c050 := path049.trans s050
  obtain ⟨c051, s051, h051⟩ := run051 h050
  have path051 : Steps c c051 := path050.trans s051
  obtain ⟨c052, s052, h052⟩ := run052 h051
  have path052 : Steps c c052 := path051.trans s052
  obtain ⟨c053, s053, h053⟩ := run053 h052
  have path053 : Steps c c053 := path052.trans s053
  obtain ⟨c054, s054, h054⟩ := run054 h053
  have path054 : Steps c c054 := path053.trans s054
  obtain ⟨c055, s055, h055⟩ := run055 h054
  have path055 : Steps c c055 := path054.trans s055
  obtain ⟨c056, s056, h056⟩ := run056 h055
  have path056 : Steps c c056 := path055.trans s056
  obtain ⟨c057, s057, h057⟩ := run057 h056
  have path057 : Steps c c057 := path056.trans s057
  obtain ⟨c058, s058, h058⟩ := run058 h057
  have path058 : Steps c c058 := path057.trans s058
  obtain ⟨c059, s059, h059⟩ := run059 h058
  have path059 : Steps c c059 := path058.trans s059
  obtain ⟨c060, s060, h060⟩ := run060 h059
  have path060 : Steps c c060 := path059.trans s060
  exact ⟨c060, path060, h060⟩

#print axioms runGroup004

theorem runGroup005 {c : Config}
    (h : TraceHolds traceD061 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD076 c' := by
  obtain ⟨c061, s061, h061⟩ := run061 h
  have path061 : Steps c c061 := s061
  obtain ⟨c062, s062, h062⟩ := run062 h061
  have path062 : Steps c c062 := path061.trans s062
  obtain ⟨c063, s063, h063⟩ := run063 h062
  have path063 : Steps c c063 := path062.trans s063
  obtain ⟨c064, s064, h064⟩ := run064 h063
  have path064 : Steps c c064 := path063.trans s064
  obtain ⟨c065, s065, h065⟩ := run065 h064
  have path065 : Steps c c065 := path064.trans s065
  obtain ⟨c066, s066, h066⟩ := run066 h065
  have path066 : Steps c c066 := path065.trans s066
  obtain ⟨c067, s067, h067⟩ := run067 h066
  have path067 : Steps c c067 := path066.trans s067
  obtain ⟨c068, s068, h068⟩ := run068 h067
  have path068 : Steps c c068 := path067.trans s068
  obtain ⟨c069, s069, h069⟩ := run069 h068
  have path069 : Steps c c069 := path068.trans s069
  obtain ⟨c070, s070, h070⟩ := run070 h069
  have path070 : Steps c c070 := path069.trans s070
  obtain ⟨c071, s071, h071⟩ := run071 h070
  have path071 : Steps c c071 := path070.trans s071
  obtain ⟨c072, s072, h072⟩ := run072 h071
  have path072 : Steps c c072 := path071.trans s072
  obtain ⟨c073, s073, h073⟩ := run073 h072
  have path073 : Steps c c073 := path072.trans s073
  obtain ⟨c074, s074, h074⟩ := run074 h073
  have path074 : Steps c c074 := path073.trans s074
  obtain ⟨c075, s075, h075⟩ := run075 h074
  have path075 : Steps c c075 := path074.trans s075
  exact ⟨c075, path075, h075⟩

#print axioms runGroup005

theorem runGroup006 {c : Config}
    (h : TraceHolds traceD076 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD091 c' := by
  obtain ⟨c076, s076, h076⟩ := run076 h
  have path076 : Steps c c076 := s076
  obtain ⟨c077, s077, h077⟩ := run077 h076
  have path077 : Steps c c077 := path076.trans s077
  obtain ⟨c078, s078, h078⟩ := run078 h077
  have path078 : Steps c c078 := path077.trans s078
  obtain ⟨c079, s079, h079⟩ := run079 h078
  have path079 : Steps c c079 := path078.trans s079
  obtain ⟨c080, s080, h080⟩ := run080 h079
  have path080 : Steps c c080 := path079.trans s080
  obtain ⟨c081, s081, h081⟩ := run081 h080
  have path081 : Steps c c081 := path080.trans s081
  obtain ⟨c082, s082, h082⟩ := run082 h081
  have path082 : Steps c c082 := path081.trans s082
  obtain ⟨c083, s083, h083⟩ := run083 h082
  have path083 : Steps c c083 := path082.trans s083
  obtain ⟨c084, s084, h084⟩ := run084 h083
  have path084 : Steps c c084 := path083.trans s084
  obtain ⟨c085, s085, h085⟩ := run085 h084
  have path085 : Steps c c085 := path084.trans s085
  obtain ⟨c086, s086, h086⟩ := run086 h085
  have path086 : Steps c c086 := path085.trans s086
  obtain ⟨c087, s087, h087⟩ := run087 h086
  have path087 : Steps c c087 := path086.trans s087
  obtain ⟨c088, s088, h088⟩ := run088 h087
  have path088 : Steps c c088 := path087.trans s088
  obtain ⟨c089, s089, h089⟩ := run089 h088
  have path089 : Steps c c089 := path088.trans s089
  obtain ⟨c090, s090, h090⟩ := run090 h089
  have path090 : Steps c c090 := path089.trans s090
  exact ⟨c090, path090, h090⟩

#print axioms runGroup006

theorem runGroup007 {c : Config}
    (h : TraceHolds traceD091 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD106 c' := by
  obtain ⟨c091, s091, h091⟩ := run091 h
  have path091 : Steps c c091 := s091
  obtain ⟨c092, s092, h092⟩ := run092 h091
  have path092 : Steps c c092 := path091.trans s092
  obtain ⟨c093, s093, h093⟩ := run093 h092
  have path093 : Steps c c093 := path092.trans s093
  obtain ⟨c094, s094, h094⟩ := run094 h093
  have path094 : Steps c c094 := path093.trans s094
  obtain ⟨c095, s095, h095⟩ := run095 h094
  have path095 : Steps c c095 := path094.trans s095
  obtain ⟨c096, s096, h096⟩ := run096 h095
  have path096 : Steps c c096 := path095.trans s096
  obtain ⟨c097, s097, h097⟩ := run097 h096
  have path097 : Steps c c097 := path096.trans s097
  obtain ⟨c098, s098, h098⟩ := run098 h097
  have path098 : Steps c c098 := path097.trans s098
  obtain ⟨c099, s099, h099⟩ := run099 h098
  have path099 : Steps c c099 := path098.trans s099
  obtain ⟨c100, s100, h100⟩ := run100 h099
  have path100 : Steps c c100 := path099.trans s100
  obtain ⟨c101, s101, h101⟩ := run101 h100
  have path101 : Steps c c101 := path100.trans s101
  obtain ⟨c102, s102, h102⟩ := run102 h101
  have path102 : Steps c c102 := path101.trans s102
  obtain ⟨c103, s103, h103⟩ := run103 h102
  have path103 : Steps c c103 := path102.trans s103
  obtain ⟨c104, s104, h104⟩ := run104 h103
  have path104 : Steps c c104 := path103.trans s104
  obtain ⟨c105, s105, h105⟩ := run105 h104
  have path105 : Steps c c105 := path104.trans s105
  exact ⟨c105, path105, h105⟩

#print axioms runGroup007

theorem runGroup008 {c : Config}
    (h : TraceHolds traceD106 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD121 c' := by
  obtain ⟨c106, s106, h106⟩ := run106 h
  have path106 : Steps c c106 := s106
  obtain ⟨c107, s107, h107⟩ := run107 h106
  have path107 : Steps c c107 := path106.trans s107
  obtain ⟨c108, s108, h108⟩ := run108 h107
  have path108 : Steps c c108 := path107.trans s108
  obtain ⟨c109, s109, h109⟩ := run109 h108
  have path109 : Steps c c109 := path108.trans s109
  obtain ⟨c110, s110, h110⟩ := run110 h109
  have path110 : Steps c c110 := path109.trans s110
  obtain ⟨c111, s111, h111⟩ := run111 h110
  have path111 : Steps c c111 := path110.trans s111
  obtain ⟨c112, s112, h112⟩ := run112 h111
  have path112 : Steps c c112 := path111.trans s112
  obtain ⟨c113, s113, h113⟩ := run113 h112
  have path113 : Steps c c113 := path112.trans s113
  obtain ⟨c114, s114, h114⟩ := run114 h113
  have path114 : Steps c c114 := path113.trans s114
  obtain ⟨c115, s115, h115⟩ := run115 h114
  have path115 : Steps c c115 := path114.trans s115
  obtain ⟨c116, s116, h116⟩ := run116 h115
  have path116 : Steps c c116 := path115.trans s116
  obtain ⟨c117, s117, h117⟩ := run117 h116
  have path117 : Steps c c117 := path116.trans s117
  obtain ⟨c118, s118, h118⟩ := run118 h117
  have path118 : Steps c c118 := path117.trans s118
  obtain ⟨c119, s119, h119⟩ := run119 h118
  have path119 : Steps c c119 := path118.trans s119
  obtain ⟨c120, s120, h120⟩ := run120 h119
  have path120 : Steps c c120 := path119.trans s120
  exact ⟨c120, path120, h120⟩

#print axioms runGroup008

theorem runGroup009 {c : Config}
    (h : TraceHolds traceD121 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD136 c' := by
  obtain ⟨c121, s121, h121⟩ := run121 h
  have path121 : Steps c c121 := s121
  obtain ⟨c122, s122, h122⟩ := run122 h121
  have path122 : Steps c c122 := path121.trans s122
  obtain ⟨c123, s123, h123⟩ := run123 h122
  have path123 : Steps c c123 := path122.trans s123
  obtain ⟨c124, s124, h124⟩ := run124 h123
  have path124 : Steps c c124 := path123.trans s124
  obtain ⟨c125, s125, h125⟩ := run125 h124
  have path125 : Steps c c125 := path124.trans s125
  obtain ⟨c126, s126, h126⟩ := run126 h125
  have path126 : Steps c c126 := path125.trans s126
  obtain ⟨c127, s127, h127⟩ := run127 h126
  have path127 : Steps c c127 := path126.trans s127
  obtain ⟨c128, s128, h128⟩ := run128 h127
  have path128 : Steps c c128 := path127.trans s128
  obtain ⟨c129, s129, h129⟩ := run129 h128
  have path129 : Steps c c129 := path128.trans s129
  obtain ⟨c130, s130, h130⟩ := run130 h129
  have path130 : Steps c c130 := path129.trans s130
  obtain ⟨c131, s131, h131⟩ := run131 h130
  have path131 : Steps c c131 := path130.trans s131
  obtain ⟨c132, s132, h132⟩ := run132 h131
  have path132 : Steps c c132 := path131.trans s132
  obtain ⟨c133, s133, h133⟩ := run133 h132
  have path133 : Steps c c133 := path132.trans s133
  obtain ⟨c134, s134, h134⟩ := run134 h133
  have path134 : Steps c c134 := path133.trans s134
  obtain ⟨c135, s135, h135⟩ := run135 h134
  have path135 : Steps c c135 := path134.trans s135
  exact ⟨c135, path135, h135⟩

#print axioms runGroup009

theorem runGroup010 {c : Config}
    (h : TraceHolds traceD136 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD151 c' := by
  obtain ⟨c136, s136, h136⟩ := run136 h
  have path136 : Steps c c136 := s136
  obtain ⟨c137, s137, h137⟩ := run137 h136
  have path137 : Steps c c137 := path136.trans s137
  obtain ⟨c138, s138, h138⟩ := run138 h137
  have path138 : Steps c c138 := path137.trans s138
  obtain ⟨c139, s139, h139⟩ := run139 h138
  have path139 : Steps c c139 := path138.trans s139
  obtain ⟨c140, s140, h140⟩ := run140 h139
  have path140 : Steps c c140 := path139.trans s140
  obtain ⟨c141, s141, h141⟩ := run141 h140
  have path141 : Steps c c141 := path140.trans s141
  obtain ⟨c142, s142, h142⟩ := run142 h141
  have path142 : Steps c c142 := path141.trans s142
  obtain ⟨c143, s143, h143⟩ := run143 h142
  have path143 : Steps c c143 := path142.trans s143
  obtain ⟨c144, s144, h144⟩ := run144 h143
  have path144 : Steps c c144 := path143.trans s144
  obtain ⟨c145, s145, h145⟩ := run145 h144
  have path145 : Steps c c145 := path144.trans s145
  obtain ⟨c146, s146, h146⟩ := run146 h145
  have path146 : Steps c c146 := path145.trans s146
  obtain ⟨c147, s147, h147⟩ := run147 h146
  have path147 : Steps c c147 := path146.trans s147
  obtain ⟨c148, s148, h148⟩ := run148 h147
  have path148 : Steps c c148 := path147.trans s148
  obtain ⟨c149, s149, h149⟩ := run149 h148
  have path149 : Steps c c149 := path148.trans s149
  obtain ⟨c150, s150, h150⟩ := run150 h149
  have path150 : Steps c c150 := path149.trans s150
  exact ⟨c150, path150, h150⟩

#print axioms runGroup010

theorem runGroup011 {c : Config}
    (h : TraceHolds traceD151 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD166 c' := by
  obtain ⟨c151, s151, h151⟩ := run151 h
  have path151 : Steps c c151 := s151
  obtain ⟨c152, s152, h152⟩ := run152 h151
  have path152 : Steps c c152 := path151.trans s152
  obtain ⟨c153, s153, h153⟩ := run153 h152
  have path153 : Steps c c153 := path152.trans s153
  obtain ⟨c154, s154, h154⟩ := run154 h153
  have path154 : Steps c c154 := path153.trans s154
  obtain ⟨c155, s155, h155⟩ := run155 h154
  have path155 : Steps c c155 := path154.trans s155
  obtain ⟨c156, s156, h156⟩ := run156 h155
  have path156 : Steps c c156 := path155.trans s156
  obtain ⟨c157, s157, h157⟩ := run157 h156
  have path157 : Steps c c157 := path156.trans s157
  obtain ⟨c158, s158, h158⟩ := run158 h157
  have path158 : Steps c c158 := path157.trans s158
  obtain ⟨c159, s159, h159⟩ := run159 h158
  have path159 : Steps c c159 := path158.trans s159
  obtain ⟨c160, s160, h160⟩ := run160 h159
  have path160 : Steps c c160 := path159.trans s160
  obtain ⟨c161, s161, h161⟩ := run161 h160
  have path161 : Steps c c161 := path160.trans s161
  obtain ⟨c162, s162, h162⟩ := run162 h161
  have path162 : Steps c c162 := path161.trans s162
  obtain ⟨c163, s163, h163⟩ := run163 h162
  have path163 : Steps c c163 := path162.trans s163
  obtain ⟨c164, s164, h164⟩ := run164 h163
  have path164 : Steps c c164 := path163.trans s164
  obtain ⟨c165, s165, h165⟩ := run165 h164
  have path165 : Steps c c165 := path164.trans s165
  exact ⟨c165, path165, h165⟩

#print axioms runGroup011

theorem runGroup012 {c : Config}
    (h : TraceHolds traceD166 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD181 c' := by
  obtain ⟨c166, s166, h166⟩ := run166 h
  have path166 : Steps c c166 := s166
  obtain ⟨c167, s167, h167⟩ := run167 h166
  have path167 : Steps c c167 := path166.trans s167
  obtain ⟨c168, s168, h168⟩ := run168 h167
  have path168 : Steps c c168 := path167.trans s168
  obtain ⟨c169, s169, h169⟩ := run169 h168
  have path169 : Steps c c169 := path168.trans s169
  obtain ⟨c170, s170, h170⟩ := run170 h169
  have path170 : Steps c c170 := path169.trans s170
  obtain ⟨c171, s171, h171⟩ := run171 h170
  have path171 : Steps c c171 := path170.trans s171
  obtain ⟨c172, s172, h172⟩ := run172 h171
  have path172 : Steps c c172 := path171.trans s172
  obtain ⟨c173, s173, h173⟩ := run173 h172
  have path173 : Steps c c173 := path172.trans s173
  obtain ⟨c174, s174, h174⟩ := run174 h173
  have path174 : Steps c c174 := path173.trans s174
  obtain ⟨c175, s175, h175⟩ := run175 h174
  have path175 : Steps c c175 := path174.trans s175
  obtain ⟨c176, s176, h176⟩ := run176 h175
  have path176 : Steps c c176 := path175.trans s176
  obtain ⟨c177, s177, h177⟩ := run177 h176
  have path177 : Steps c c177 := path176.trans s177
  obtain ⟨c178, s178, h178⟩ := run178 h177
  have path178 : Steps c c178 := path177.trans s178
  obtain ⟨c179, s179, h179⟩ := run179 h178
  have path179 : Steps c c179 := path178.trans s179
  obtain ⟨c180, s180, h180⟩ := run180 h179
  have path180 : Steps c c180 := path179.trans s180
  exact ⟨c180, path180, h180⟩

#print axioms runGroup012

theorem runGroup013 {c : Config}
    (h : TraceHolds traceD181 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD196 c' := by
  obtain ⟨c181, s181, h181⟩ := run181 h
  have path181 : Steps c c181 := s181
  obtain ⟨c182, s182, h182⟩ := run182 h181
  have path182 : Steps c c182 := path181.trans s182
  obtain ⟨c183, s183, h183⟩ := run183 h182
  have path183 : Steps c c183 := path182.trans s183
  obtain ⟨c184, s184, h184⟩ := run184 h183
  have path184 : Steps c c184 := path183.trans s184
  obtain ⟨c185, s185, h185⟩ := run185 h184
  have path185 : Steps c c185 := path184.trans s185
  obtain ⟨c186, s186, h186⟩ := run186 h185
  have path186 : Steps c c186 := path185.trans s186
  obtain ⟨c187, s187, h187⟩ := run187 h186
  have path187 : Steps c c187 := path186.trans s187
  obtain ⟨c188, s188, h188⟩ := run188 h187
  have path188 : Steps c c188 := path187.trans s188
  obtain ⟨c189, s189, h189⟩ := run189 h188
  have path189 : Steps c c189 := path188.trans s189
  obtain ⟨c190, s190, h190⟩ := run190 h189
  have path190 : Steps c c190 := path189.trans s190
  obtain ⟨c191, s191, h191⟩ := run191 h190
  have path191 : Steps c c191 := path190.trans s191
  obtain ⟨c192, s192, h192⟩ := run192 h191
  have path192 : Steps c c192 := path191.trans s192
  obtain ⟨c193, s193, h193⟩ := run193 h192
  have path193 : Steps c c193 := path192.trans s193
  obtain ⟨c194, s194, h194⟩ := run194 h193
  have path194 : Steps c c194 := path193.trans s194
  obtain ⟨c195, s195, h195⟩ := run195 h194
  have path195 : Steps c c195 := path194.trans s195
  exact ⟨c195, path195, h195⟩

#print axioms runGroup013

theorem runGroup014 {c : Config}
    (h : TraceHolds traceD196 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD211 c' := by
  obtain ⟨c196, s196, h196⟩ := run196 h
  have path196 : Steps c c196 := s196
  obtain ⟨c197, s197, h197⟩ := run197 h196
  have path197 : Steps c c197 := path196.trans s197
  obtain ⟨c198, s198, h198⟩ := run198 h197
  have path198 : Steps c c198 := path197.trans s198
  obtain ⟨c199, s199, h199⟩ := run199 h198
  have path199 : Steps c c199 := path198.trans s199
  obtain ⟨c200, s200, h200⟩ := run200 h199
  have path200 : Steps c c200 := path199.trans s200
  obtain ⟨c201, s201, h201⟩ := run201 h200
  have path201 : Steps c c201 := path200.trans s201
  obtain ⟨c202, s202, h202⟩ := run202 h201
  have path202 : Steps c c202 := path201.trans s202
  obtain ⟨c203, s203, h203⟩ := run203 h202
  have path203 : Steps c c203 := path202.trans s203
  obtain ⟨c204, s204, h204⟩ := run204 h203
  have path204 : Steps c c204 := path203.trans s204
  obtain ⟨c205, s205, h205⟩ := run205 h204
  have path205 : Steps c c205 := path204.trans s205
  obtain ⟨c206, s206, h206⟩ := run206 h205
  have path206 : Steps c c206 := path205.trans s206
  obtain ⟨c207, s207, h207⟩ := run207 h206
  have path207 : Steps c c207 := path206.trans s207
  obtain ⟨c208, s208, h208⟩ := run208 h207
  have path208 : Steps c c208 := path207.trans s208
  obtain ⟨c209, s209, h209⟩ := run209 h208
  have path209 : Steps c c209 := path208.trans s209
  obtain ⟨c210, s210, h210⟩ := run210 h209
  have path210 : Steps c c210 := path209.trans s210
  exact ⟨c210, path210, h210⟩

#print axioms runGroup014

theorem runGroup015 {c : Config}
    (h : TraceHolds traceD211 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD226 c' := by
  obtain ⟨c211, s211, h211⟩ := run211 h
  have path211 : Steps c c211 := s211
  obtain ⟨c212, s212, h212⟩ := run212 h211
  have path212 : Steps c c212 := path211.trans s212
  obtain ⟨c213, s213, h213⟩ := run213 h212
  have path213 : Steps c c213 := path212.trans s213
  obtain ⟨c214, s214, h214⟩ := run214 h213
  have path214 : Steps c c214 := path213.trans s214
  obtain ⟨c215, s215, h215⟩ := run215 h214
  have path215 : Steps c c215 := path214.trans s215
  obtain ⟨c216, s216, h216⟩ := run216 h215
  have path216 : Steps c c216 := path215.trans s216
  obtain ⟨c217, s217, h217⟩ := run217 h216
  have path217 : Steps c c217 := path216.trans s217
  obtain ⟨c218, s218, h218⟩ := run218 h217
  have path218 : Steps c c218 := path217.trans s218
  obtain ⟨c219, s219, h219⟩ := run219 h218
  have path219 : Steps c c219 := path218.trans s219
  obtain ⟨c220, s220, h220⟩ := run220 h219
  have path220 : Steps c c220 := path219.trans s220
  obtain ⟨c221, s221, h221⟩ := run221 h220
  have path221 : Steps c c221 := path220.trans s221
  obtain ⟨c222, s222, h222⟩ := run222 h221
  have path222 : Steps c c222 := path221.trans s222
  obtain ⟨c223, s223, h223⟩ := run223 h222
  have path223 : Steps c c223 := path222.trans s223
  obtain ⟨c224, s224, h224⟩ := run224 h223
  have path224 : Steps c c224 := path223.trans s224
  obtain ⟨c225, s225, h225⟩ := run225 h224
  have path225 : Steps c c225 := path224.trans s225
  exact ⟨c225, path225, h225⟩

#print axioms runGroup015

theorem runGroup016 {c : Config}
    (h : TraceHolds traceD226 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD241 c' := by
  obtain ⟨c226, s226, h226⟩ := run226 h
  have path226 : Steps c c226 := s226
  obtain ⟨c227, s227, h227⟩ := run227 h226
  have path227 : Steps c c227 := path226.trans s227
  obtain ⟨c228, s228, h228⟩ := run228 h227
  have path228 : Steps c c228 := path227.trans s228
  obtain ⟨c229, s229, h229⟩ := run229 h228
  have path229 : Steps c c229 := path228.trans s229
  obtain ⟨c230, s230, h230⟩ := run230 h229
  have path230 : Steps c c230 := path229.trans s230
  obtain ⟨c231, s231, h231⟩ := run231 h230
  have path231 : Steps c c231 := path230.trans s231
  obtain ⟨c232, s232, h232⟩ := run232 h231
  have path232 : Steps c c232 := path231.trans s232
  obtain ⟨c233, s233, h233⟩ := run233 h232
  have path233 : Steps c c233 := path232.trans s233
  obtain ⟨c234, s234, h234⟩ := run234 h233
  have path234 : Steps c c234 := path233.trans s234
  obtain ⟨c235, s235, h235⟩ := run235 h234
  have path235 : Steps c c235 := path234.trans s235
  obtain ⟨c236, s236, h236⟩ := run236 h235
  have path236 : Steps c c236 := path235.trans s236
  obtain ⟨c237, s237, h237⟩ := run237 h236
  have path237 : Steps c c237 := path236.trans s237
  obtain ⟨c238, s238, h238⟩ := run238 h237
  have path238 : Steps c c238 := path237.trans s238
  obtain ⟨c239, s239, h239⟩ := run239 h238
  have path239 : Steps c c239 := path238.trans s239
  obtain ⟨c240, s240, h240⟩ := run240 h239
  have path240 : Steps c c240 := path239.trans s240
  exact ⟨c240, path240, h240⟩

#print axioms runGroup016

theorem runGroup017 {c : Config}
    (h : TraceHolds traceD241 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD256 c' := by
  obtain ⟨c241, s241, h241⟩ := run241 h
  have path241 : Steps c c241 := s241
  obtain ⟨c242, s242, h242⟩ := run242 h241
  have path242 : Steps c c242 := path241.trans s242
  obtain ⟨c243, s243, h243⟩ := run243 h242
  have path243 : Steps c c243 := path242.trans s243
  obtain ⟨c244, s244, h244⟩ := run244 h243
  have path244 : Steps c c244 := path243.trans s244
  obtain ⟨c245, s245, h245⟩ := run245 h244
  have path245 : Steps c c245 := path244.trans s245
  obtain ⟨c246, s246, h246⟩ := run246 h245
  have path246 : Steps c c246 := path245.trans s246
  obtain ⟨c247, s247, h247⟩ := run247 h246
  have path247 : Steps c c247 := path246.trans s247
  obtain ⟨c248, s248, h248⟩ := run248 h247
  have path248 : Steps c c248 := path247.trans s248
  obtain ⟨c249, s249, h249⟩ := run249 h248
  have path249 : Steps c c249 := path248.trans s249
  obtain ⟨c250, s250, h250⟩ := run250 h249
  have path250 : Steps c c250 := path249.trans s250
  obtain ⟨c251, s251, h251⟩ := run251 h250
  have path251 : Steps c c251 := path250.trans s251
  obtain ⟨c252, s252, h252⟩ := run252 h251
  have path252 : Steps c c252 := path251.trans s252
  obtain ⟨c253, s253, h253⟩ := run253 h252
  have path253 : Steps c c253 := path252.trans s253
  obtain ⟨c254, s254, h254⟩ := run254 h253
  have path254 : Steps c c254 := path253.trans s254
  obtain ⟨c255, s255, h255⟩ := run255 h254
  have path255 : Steps c c255 := path254.trans s255
  exact ⟨c255, path255, h255⟩

#print axioms runGroup017

theorem runGroup018 {c : Config}
    (h : TraceHolds traceD256 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD271 c' := by
  obtain ⟨c256, s256, h256⟩ := run256 h
  have path256 : Steps c c256 := s256
  obtain ⟨c257, s257, h257⟩ := run257 h256
  have path257 : Steps c c257 := path256.trans s257
  obtain ⟨c258, s258, h258⟩ := run258 h257
  have path258 : Steps c c258 := path257.trans s258
  obtain ⟨c259, s259, h259⟩ := run259 h258
  have path259 : Steps c c259 := path258.trans s259
  obtain ⟨c260, s260, h260⟩ := run260 h259
  have path260 : Steps c c260 := path259.trans s260
  obtain ⟨c261, s261, h261⟩ := run261 h260
  have path261 : Steps c c261 := path260.trans s261
  obtain ⟨c262, s262, h262⟩ := run262 h261
  have path262 : Steps c c262 := path261.trans s262
  obtain ⟨c263, s263, h263⟩ := run263 h262
  have path263 : Steps c c263 := path262.trans s263
  obtain ⟨c264, s264, h264⟩ := run264 h263
  have path264 : Steps c c264 := path263.trans s264
  obtain ⟨c265, s265, h265⟩ := run265 h264
  have path265 : Steps c c265 := path264.trans s265
  obtain ⟨c266, s266, h266⟩ := run266 h265
  have path266 : Steps c c266 := path265.trans s266
  obtain ⟨c267, s267, h267⟩ := run267 h266
  have path267 : Steps c c267 := path266.trans s267
  obtain ⟨c268, s268, h268⟩ := run268 h267
  have path268 : Steps c c268 := path267.trans s268
  obtain ⟨c269, s269, h269⟩ := run269 h268
  have path269 : Steps c c269 := path268.trans s269
  obtain ⟨c270, s270, h270⟩ := run270 h269
  have path270 : Steps c c270 := path269.trans s270
  exact ⟨c270, path270, h270⟩

#print axioms runGroup018

theorem runGroup019 {c : Config}
    (h : TraceHolds traceD271 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD285 c' := by
  obtain ⟨c271, s271, h271⟩ := run271 h
  have path271 : Steps c c271 := s271
  obtain ⟨c272, s272, h272⟩ := run272 h271
  have path272 : Steps c c272 := path271.trans s272
  obtain ⟨c273, s273, h273⟩ := run273 h272
  have path273 : Steps c c273 := path272.trans s273
  obtain ⟨c274, s274, h274⟩ := run274 h273
  have path274 : Steps c c274 := path273.trans s274
  obtain ⟨c275, s275, h275⟩ := run275 h274
  have path275 : Steps c c275 := path274.trans s275
  obtain ⟨c276, s276, h276⟩ := run276 h275
  have path276 : Steps c c276 := path275.trans s276
  obtain ⟨c277, s277, h277⟩ := run277 h276
  have path277 : Steps c c277 := path276.trans s277
  obtain ⟨c278, s278, h278⟩ := run278 h277
  have path278 : Steps c c278 := path277.trans s278
  obtain ⟨c279, s279, h279⟩ := run279 h278
  have path279 : Steps c c279 := path278.trans s279
  obtain ⟨c280, s280, h280⟩ := run280 h279
  have path280 : Steps c c280 := path279.trans s280
  obtain ⟨c281, s281, h281⟩ := run281 h280
  have path281 : Steps c c281 := path280.trans s281
  obtain ⟨c282, s282, h282⟩ := run282 h281
  have path282 : Steps c c282 := path281.trans s282
  obtain ⟨c283, s283, h283⟩ := run283 h282
  have path283 : Steps c c283 := path282.trans s283
  obtain ⟨c284, s284, h284⟩ := run284 h283
  have path284 : Steps c c284 := path283.trans s284
  exact ⟨c284, path284, h284⟩

#print axioms runGroup019

end Vsa.Sim.OutputAliasLoaded
