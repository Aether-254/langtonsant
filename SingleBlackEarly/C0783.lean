import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0783 : checkSingleBlackFast (24, -13) 10480 .north (-2, 0) (-26, 2) = true := by
  decide +kernel

end LangtonsAnt
