import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2149 : checkSingleBlackFast (-88, -62) 14084 .north (33, 25) (-59, -41) = true := by
  decide +kernel

end LangtonsAnt
