import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2084 : checkSingleBlackFast (-83, -56) 19978 .north (33, 26) (-60, -39) = true := by
  decide +kernel

end LangtonsAnt
