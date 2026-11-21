import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1437 : checkSingleBlackFast (-20, -1) 24900 .south (-4, -11) (-18, -23) = true := by
  decide +kernel

end LangtonsAnt
