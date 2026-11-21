import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1155 : checkSingleBlackFast (19, -22) 10480 .north (-1, 2) (-25, 4) = true := by
  decide +kernel

end LangtonsAnt
