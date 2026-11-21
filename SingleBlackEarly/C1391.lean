import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1391 : checkSingleBlackFast (-17, 3) 21592 .north (-1, 1) (-5, -37) = true := by
  decide +kernel

end LangtonsAnt
