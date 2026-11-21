import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1120 : checkSingleBlackFast (25, -13) 10276 .north (-2, -2) (-26, 0) = true := by
  decide +kernel

end LangtonsAnt
