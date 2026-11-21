import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1161 : checkSingleBlackFast (26, -13) 10488 .north (-2, 0) (-26, 2) = true := by
  decide +kernel

end LangtonsAnt
