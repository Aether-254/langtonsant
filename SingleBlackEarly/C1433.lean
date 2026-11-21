import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1433 : checkSingleBlackFast (-23, 1) 24256 .north (-3, 6) (-9, -34) = true := by
  decide +kernel

end LangtonsAnt
