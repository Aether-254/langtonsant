import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0075 : checkSingleBlackFast (4, -5) 6836 .north (-1, 0) (-17, -16) = true := by
  decide +kernel

end LangtonsAnt
