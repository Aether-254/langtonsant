import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1912 : checkSingleBlackFast2 (-65, -43) 16105 .west (20, 29) (-49, 9) = true := by
  decide +kernel

end LangtonsAnt
