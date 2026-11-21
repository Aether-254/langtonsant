import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0856 : checkSingleBlackFast (-9, 7) 7890 .north (1, 1) (-24, -10) = true := by
  decide +kernel

end LangtonsAnt
