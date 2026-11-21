import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1719 : checkSingleBlackFast (-49, -25) 13847 .west (11, 22) (-41, 3) = true := by
  decide +kernel

end LangtonsAnt
