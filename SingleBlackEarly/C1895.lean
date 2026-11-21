import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1895 : checkSingleBlackFast (-65, -41) 14679 .west (19, 30) (-49, 11) = true := by
  decide +kernel

end LangtonsAnt
