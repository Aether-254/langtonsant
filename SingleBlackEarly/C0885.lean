import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0885 : checkSingleBlackFast (-9, -2) 9284 .north (-1, -2) (-23, 2) = true := by
  decide +kernel

end LangtonsAnt
